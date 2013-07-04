
export Symbolic, AbstractVariable, SymbolicVariable, BasicVariable, processExpr, @sexpr
export SymbolParameter, simplify 
import Base.show, Base.(==)

#################################################################
#
# Symbolic types
#   Symbolic - top of the tree
#   AbstractVariable - inherit from this for custom symbolic
#                      variable types
#   SymbolicVariable - use this in method argument typing
#
#################################################################

abstract Symbolic
abstract AbstractVariable <: Symbolic
typealias SymbolicVariable Union(Symbol, AbstractVariable)


#################################################################
#
# BasicVariable - an example to use during testing
#
#################################################################

type BasicVariable <: AbstractVariable
    sym::Symbol
end
# The following is probably too plain.
show(io::IO, x::BasicVariable) = print(io, x.sym)
(==)(x::BasicVariable, y::BasicVariable) = x.sym == y.sym


#################################################################
#
# @sexpr - return an Expr with variables spliced in
# processExpr - do the Expr splicing
#
#################################################################

function processExpr(x::Expr)
    if x.head == :call
        quoted = Expr(:quote,x.args[1])
        code = :(Expr(:call,$quoted))
        for y in x.args[2:end]
            push!(code.args,processExpr(y))
        end
        return code
    else
        return x
    end
end

processExpr(x::Any) = x

macro sexpr(x)
    esc(processExpr(x))
end


#################################################################
#
# SymbolParameter
#   used to be able to dispatch on the symbol representing a
#   function
#   
#################################################################

type SymbolParameter{T}
end
SymbolParameter(s::Symbol) = SymbolParameter{s}()



#################################################################
#
# simplify()
#   
#################################################################


# Numbers and symbols can't be simplified further
simplify(x) = x
simplify(n::Number) = n
simplify(s::SymbolicVariable) = s

# The default is just to simplify arguments.
simplify{T}(x::SymbolParameter{T}, args) = Expr(:call, T, map(x -> simplify(x), args)...)

function simplify(ex::Expr)
    if ex.head != :call
        return ex
    end
    if all(map(a -> isa(a, Number), ex.args[2:end]))
        return eval(ex)
    end
    new_ex = simplify(SymbolParameter(ex.args[1]), ex.args[2:end])
    while new_ex != ex
        new_ex, ex = simplify(new_ex), new_ex
    end
    return new_ex
end

function comp_args(a::Expr, b::Expr)
    # can we have expressions of other types than call
    assert(a.head == b.head == :call)
    s_a, s_b = string(a.args[1]), string(b.args[1])
    if s_a == s_b
        for (a_s, b_s) in zip(a.args[2:],b.args[2:])
            if isequal(a_s,b_s)
                continue
            end
            return comp_args(a_s, b_s)
        end
    else
        return s_a < s_b
    end
    #the args are strictly equal
    return true
end
comp_args(a::Number, b::Number) = a<b
comp_args(a::Symbol, b::Symbol) = return string(a)<string(b)
function comp_args(a,b)
    if isa(a, Number)
        return true
    elseif isa(b, Number)
        return false
    elseif isa(a, Symbol)
        return true
    elseif isa(b, Symbol)
        return false
    elseif isa(a, Expr)
        return true
    elseif isa(b,Expr)
        return false
    elseif isa(a, BasicVariable)
        return false
    elseif isa(b, BasicVariable)
        return true
    else
        error("Unknown arguments ", typeof(a), " ", typeof(b))
    end
end



# Handles all lengths for ex.args
# precomputes numeric parts of a sum
function simplify(::SymbolParameter{:+}, args)
    new_args = Any[]
    numeric = 0
    for arg in args
        arg = simplify(arg)
        if isa(arg, Number)
            numeric = numeric + arg
        else
            if issubcall(arg, :+)
                new_args = vcat(new_args, arg.args[2:end])
            elseif issubcall(arg, :-) && length(arg.args) == 2
                #search for something to match the negative
                found = false
                for i = 1:length(new_args)
                    if isequal(new_args[i],arg.args[2])
                        splice!(new_args,i)
                        found = true
                        break
                    end
                end
                if !found
                    push!(new_args, arg)
                end
            else
                push!(new_args,arg)
            end
        end
    end

    # order arguments for canonicalisation
    sort!(new_args, Sort.InsertionSort, comp_args)

    #find duplicates and replace a+a with 2*a
    l_new_args = length(new_args)
    remove = falses(l_new_args)
    for i = 1:(l_new_args-1)
        if remove[i]
            continue
        end
        count = 1
        for j = (i+1):l_new_args
            if isequal(new_args[i],new_args[j])
                remove[j] = true
                count = count + 1
            end
        end
        if count > 1
            new_args[i] = Expr(:call, :*, count, new_args[i])
        end
    end
    for i in length(remove):-1:1
        if remove[i]
            splice!(new_args, i)
        end
    end

    if length(new_args) == 0
        return numeric
    # Special Case: simplify(:(+x)) == x
    elseif length(new_args) == 1 && numeric == 0
        return new_args[1]
    elseif numeric == 0
        return Expr(:call, :+, new_args...)
    else
        return Expr(:call, :+, numeric, new_args...)
    end
end

# translates the expression to + and lets it handle the trouble
function simplify(::SymbolParameter{:-}, args)
    if length(args) == 1
        arg = simplify(args[1])
        if isa(arg, Expr) && arg.head == :call
            if arg.args[1] == :- && length(arg.args) == 2
                return arg
            elseif arg.args[1] == :+
                new_args = Any[]
                for arg in arg.args[2:]
                    push!(new_args, Expr(:call, :-, arg))
                end
                return Expr(:call, :+, new_args...)
            end
        end
        return Expr(:call, :-, arg)
    else
        new_args = Any[]
        for arg in args[2:]
            push!(new_args, Expr(:call, :-, arg))
        end
    end
    return Expr(:call, :+, args[1], new_args...)
end

# Handles all lengths for ex.args
# Precomputes numeric constants in ex.args, and special cases 0,1,-1
function simplify(::SymbolParameter{:*}, args)
    new_args = Any[]
    numeric = 1
    for arg in args
        a = simplify(arg)
        if isa(a, Number)
            numeric = numeric*a
        else
            if issubcall(a,:*)
                new_args = vcat(new_args,a.args[2:end])
            elseif numeric != 1 && issubcall(a, :-) && length(a.args) == 2
                numeric = -numeric
                push!(new_args, a.args[2])
            else
                push!(new_args,a)
            end
        end
    end
    if numeric == 0
        return 0
    elseif length(new_args) == 0
        return numeric
    elseif numeric == -1 && length(new_args) == 1
        # *(-1,x) -> -(x)
        return Expr(:call, :-, new_args...)
    elseif numeric == 1 && length(new_args) == 1
        # 1*x -> x
        return new_args[1]
    elseif numeric == 1
        # 1*x*z -> x*z
        return Expr(:call, :*, new_args...)
    else
        return Expr(:call, :*, numeric, new_args...)
    end
end

# Assumes length(ex.args) == 3
function simplify(::SymbolParameter{:/}, args)
    new_args = map(x -> simplify(x), args)
    # Special Case: simplify(:(x / 1)) == x
    if new_args[2] == 1
        return new_args[1]
    # Special Case: simplify(:(0 / x)) == 0
    elseif new_args[1] == 0
        return 0
    else
        return Expr(:call, :/, new_args...)
    end
end

# Assumes length(ex.args) == 3
function simplify(::SymbolParameter{:^}, args)
    new_args = map(x -> simplify(x), args)
    # Special Case: simplify(:(x ^ 0)) == 1
    if new_args[2] == 0
        return 1
    # Special Case: simplify(:(x ^ 1)) == x
    elseif new_args[2] == 1
        return new_args[1]
    # Special Case: simplify(:(0 ^ x)) == 0
    elseif new_args[1] == 0
        return 0
    # Special Case: simplify(:(1 ^ x)) == 1
    elseif new_args[1] == 1
        return 1
    else
        return Expr(:call, :^, new_args...)
    end
end

issubcall(a, fun::Symbol) = isa(a,Expr) && a.head == :call && a.args[1] == fun
