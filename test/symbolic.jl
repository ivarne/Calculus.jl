# Test simplify(e::Expr)
eqsimp(a,b) = isequal(simplify(a),b)
@assert eqsimp(:(x^0+5),6)
@assert eqsimp(:(z^1*cos(z)),:(z*cos(z)))
@assert eqsimp(:(6*2.*5*3),180.)
@assert eqsimp(:(b+a),:(a+b))
@assert eqsimp(:((a*b)*c),:(a*b*c))
@assert eqsimp(:((a+b)+c),:(a+b+c))
@assert eqsimp(:((a+5)+4+b),:(9+a+b))
@assert eqsimp(:(a+(b-a)),:(b))
@assert eqsimp(:(a+b-a+b),:(2b))
@assert eqsimp(:((a+b)-(a+b)),0)
# ensure simplify does not break matrix multiplication rules
@assert !eqsimp(:(a*b),:(b*a))
@assert !eqsimp(:(b*a),:(a*b))

#
# Univariate Calculus
#
function assert_differentiate(y, x, y_der)
	y_der_sym = differentiate(y,x)
	if isequal(simplify(y_der_sym),simplify(y_der))
		return nothing
	end
	error("differentiate(",y,", ",x,") = ",y_der_sym," is not equivalent to ",y_der)
end
assert_differentiate(:(2), :x, 0)
assert_differentiate(:(x), :x, 1)
assert_differentiate(:(x + x), :x, 2)
assert_differentiate(:(x - x), :x, 0)
assert_differentiate(:(2 * x), :x, 2)
assert_differentiate(:(2 / x), :x, :(-2 / x^2))
assert_differentiate(:(x / 2), :x, 0.5)
assert_differentiate(:(sin(x) / x), :x, :((cos(x) * x - sin(x)) / x^2))
assert_differentiate(:(x * 2), :x, 2)
assert_differentiate(:(a * x), :x, :a)
assert_differentiate(:(x * a), :x, :a)
assert_differentiate(:(x ^ 2), :x, :(2 * x))
assert_differentiate(:(a * x ^ 2), :x, :(a * (2 * x)))
assert_differentiate(:(2 ^ x), :x, :(*(^(2, x), 0.6931471805599453)))
assert_differentiate(:(sin(x)), :x, :(cos(x)))
assert_differentiate(:(cos(x)), :x, :(*(-1,sin(x))))  # needs a better simplify
assert_differentiate(:(tan(x)), :x, :(1 + tan(x)^2))
assert_differentiate(:(exp(x)), :x, :(exp(x)))
assert_differentiate(:(log(x)), :x, :(1 / x))
assert_differentiate(:(sin(x) + sin(x)), :x, :(cos(x) + cos(x)))
assert_differentiate(:(sin(x) - cos(x)), :x, :(-(cos(x),*(-1,sin(x))))) # Simplify -(a, -(b)) => +(a, b)
assert_differentiate(:(x * sin(x)), :x, :(sin(x) + x * cos(x)))
assert_differentiate(:(x / sin(x)), :x, :((sin(x) - x * cos(x)) / (sin(x)^2)))
assert_differentiate(:(sin(sin(x))), :x, :(*(cos(x),cos(sin(x)))))
assert_differentiate(:(sin(cos(x) + sin(x))), :x, :(*(+(*(-1,sin(x)),cos(x)),cos(+(cos(x),sin(x)))))) # Clean this up
assert_differentiate(:(exp(-x)), :x, :(*(-1,exp(-(x))))) # Simplify this to -(exp(-x))
assert_differentiate(:(log(x^2)), :x, :(/(*(2,x),^(x,2))))
assert_differentiate(:(x^n), :x, :(*(n, ^(x, -(n, 1)))))
assert_differentiate(:(n^x), :x, :(*(^(n, x), log(n))))
assert_differentiate(:(n^n), :x, 0)

#
# Multivariate Calculus
#

assert_differentiate(:(sin(x) + sin(y)), [:x, :y], [:(cos(x)), :(cos(y))])

# TODO: Get the generalized power rule right.
# @assert isequal(differentiate(:(sin(x)^2), :x), :(2 * sin(x) * cos(x)))

#
# Strings instead of symbols
#

# @assert isequal(differentiate("sin(x) + cos(x)^2"), :(+(cos(x),*(2,cos(x)))))
assert_differentiate("x + exp(-x) + sin(exp(x))", :x, :(+(1,*(-1,exp(-(x))),*(exp(x),cos(exp(x))))))

# TODO: Make these work
# differentiate(:(sin(x)), :x)(0.0)
# differentiate(:(sin(x)), :x)(1.0)
# differentiate(:(sin(x)), :x)(pi)

#
# SymbolicVariable use
#

x = BasicVariable(:x)
y = BasicVariable(:y)

@assert isequal(@sexpr(x + y), :($x + $y))
@assert isequal(differentiate(@sexpr(3 * x), x), 3)
@assert isequal(differentiate(:(sin(sin(x))), :x), :(*(cos(x),cos(sin(x)))))
@assert isequal(differentiate(@sexpr(sin(sin(x))), x), :(*(cos($x),cos(sin($x)))))

function testfun(x)
    z = BasicVariable(:z)
    differentiate(@sexpr(3*x + x^2*z), z)
end

@assert isequal(testfun(x), :(^($(x),2)))
@assert isequal(testfun(3), 9)
@assert isequal(testfun(@sexpr(x+y)), :(^(+($x,$y),2)))
