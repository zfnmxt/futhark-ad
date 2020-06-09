# Forward mode

Consider the program

    x_1 = <input>
    x_2 = <input>
    x_3 = x_1 * x_2
    x_4 = x_3 * x_1
    x_5 = x_3 * x_4
	
In forward-mode automatic differentiation, we wish to compute the
derivative of each variable `x_i` with respect to some
intput variable (`x_1` or `x_2`). That is, our objective is to compute
the tangent variable

    x_i' = dx_i/x_*
	
for each `i`, with `* = 1` or `* = 2`. This can be done by direct
application of the chain rule. For example,

    dx_5/dx_1 = (dx_5/dx_3) * (dx_3/dx_1) + (dx_5/dx_4) * (dx_4/dx_1)
	          = (dx_5/dx_3) * x_3' + (dx_5/dx_4) * x_4'
			  = x_4 * x_3' + x_3 * x_4'

This means that we can build-up the derivatives of any intermediate 
variable by first computing the derivative of all the variables
it directly depends upon (and so on) and then using the chain rule.
This is the principle idea of forward-mode differentiation.

A crucial point here is that we only need "local" information to 
build the intermediate derivative. Given

    x_5 = x_3 * x_4
	
we immediately can write

    x_5' = x_4 * x_3' + x_3 * x_4'
	
trusting that previous steps computed `x_3'` and `x_4'`. This has the
consequence that we do not care if `* = 1` or `* = 2`. We choose `* =
1` by setting `(x_1', x_2) = (1, 0)` or `* = 2` with `(x_1', x_2) =
(0, 1)`; the symbolic manipulation is unchanged. This works because,
in the case with `* = 1`, any derivative components which depend on
`x_2'` will do so via a multiplicative factor (due to the chain rule) and
hence will be zeroed out by `x_2' = 0` (and likewise, factors that
depend on `x_1'` will be "chosen" by `x_1' = 1`).

## Implementation

For each source variable `x_i` we associate a corresponding 
tangent variable `x_i'` and provide a mapping `D : Primal -> Tangent`
from the primal variables to their tangent counterparts.

We traverse the source program from top-to-bottom. For each statement
of the form

    x_i = f(x_j, x_k, ..., x_l)

we compute 

    x_i' = f' x_j' + f' x_k' + ... + f' x_l'
	
Since we start from top-to-bottom, the derivatives `x_j', x_k', ...,
x_l'` have all already been computed (each index is `< i`).

We can insert the tangent statement directly after the primal
statement since all dependencies of the tangent statement
will have already been defined before.

So, to take the forward-mode derivative of a program, we simply traverse
the program once, top-to-bottom and insert the tangent statement
directly after its corresponding primal statement.

# Reverse mode

Again, we consider the program

    x_1 = <input>
    x_2 = <input>
    x_3 = x_1 * x_2
    x_4 = x_3 * x_1
    x_5 = x_3 * x_4

Reverse mode asks if we can compute the derivative in a bottom-up traversal 
by computing adjoints of variables, defined by

    |x_i| = dx_5/dx_i
	
where we conider `x_5` to be the output of the program. The
distinction between tangent `x_i'` (from the forward mode) and the
adjoint `|x_i|` that the tangent *fixes the derivative with respect
to a given input variable* whereas the adjoint of `x_i` is the
*derivative of a given output variable with respect to `x_i`*.

Again, we build the adjoints of each variable via the chain-rule, since

    |x_i| = dx_5/dx_i 
	         = sum_{j, x_j is a function of x_i} (dx_5/dx_j)(dx_j/dx_i)
	         = sum_{j, x_j is a function of x_i} |x_j|(dx_j/dx_i)
	
where the condition `x_j is a function x_i` just means that `x_i` appears on the
RHS of a statement setting `x_j`. At the end, we end up with `|x_1| = dx_5/dx_1`
and `|x_2| = dx_5/dx_2`, the quantities of interest.

Note that in a single pass, we were able to retrieve both `|x_1|` and `|x_2`;
with forward mode this would've taken two passes (once with `x_1' = 1` and
once with `x_2' = 1`). For a given output variable, reverse mode retrieves all partial
derivatives (that is, it retrieves a *row* of the Jacobian of the program) of that output.

On the other hand, forward mode retrieves all a partial derivative for each output, given 
an input. For vector-valued functions, this means that we obtain a *column* of the Jacobian
of the program.

## Implementation

Since adjoints are a sum of components, we have to traverse the program multiple times.
In the first pass, we construct a map `A : Primal -> (Adjoint, Exp)` from primal variables
to a tuple of the correspnding adjoint variable as well as an expression for the adjoint itself.
Given a statement

    x_i = f(x_j, x_k, ..., x_l)
	
we modify the entries for `x_j, x_k, ..., x_l` in `A` with

    map (\x -> insertWith (+) x (|x_i| * (dx_i/dx)))  [x_j, x_k, ..., x_l]
	
That is, for each RHS variable, we add to its adjoint the sensitivity
of the variable output to `x_i` (expressed by `|x_i|`) multiple by the
variable's sensitivity to `x_i` itself.

Once this map is constructed, all that remains is to insert adjoint
statements into the program, where the RHS is given by the expressions
in the map.  Inserting adjoints must be done judiciously; we cannot
insert an adjoint until all of its dependencies are already inserted.
For a primal `x_i`, these dependencies take the form of the adjoints
of LHS variables in statements that `x_i` appears on the RHS of, say `|x_j|`.
Additionally any dependency of `dx_j/dx_i` must have also already appeared,
but `dx_j/dx_i` will only consist of primal variables (appearing before `x_j`).

Since `x_j` depends directly on `x_i`, `x_i` must have be defined 
*before* `x_j` in the program. So, `|x_i|` only depends on 
the adjoints of variables that appear after `x_i` in the program.
This means that we can simply insert all adjoints in reverse-order
after the primal statements of the program in order to 
satisfy data dependencies:

    x_1 = <input>
    x_2 = <input>
    x_3 = x_1 * x_2
    x_4 = x_3 * x_1
    x_5 = x_3 * x_4
	|x_5| = ...
	|x_4| = ...
	.
	.
	.
	|x_1| = ...

# Mixed mode:




## An example

The idea here is to do reverse-mode normally and take forward-mode
derivatives of expressions that are difficult to do in reverse-mode.

Consider:

    x_1 = <input>
    x_2 = <input>
    x_3 = x_1 * x_2
    x_4 = x_1 + x_3
    x_5 = loop acc = x_4 for i < 2 do  -- computes (x_4)^3
            acc * x_4
    x_6 = x_5 + x_4

We traverse the statements top-to-bottom. For each statement of the
form `x_l = f(x_{r, 0}, x_{r_1}, ..., x_{r,n})` we insert n adjoint
variables `bar(x_{r,i})` into a map associating normal variables with
their adjoints:

    bar(x_{r,i}) += dx_6/d(x_{r,i}) = bar(x_l) dx_l/d(x_{r,i})

This is easy to do for statements like `x_3 = x_1 * x_2` since

    bar(x_1) = bar(x_3) dx_3/dx_1 = bar(x_3) x_2

But it's not straightforward how to compute `bar(x_4)` since the
derivative `dx_5/dx_4` is not readily available.

However, forward-mode gives us exactly the derivative (`dx_5/dx_4`)
that we need. Namely, taking the forward-mode derivative of

    x_5 = loop acc = x_4 for i < 2 do
            acc * x_4

yields a statement of the form

    (x_5, x_5') = loop (acc = x_4, acc' = x_4') for i < 2 do
                    (acc * x_4, acc' * x_4 + acc * x_4')

Unrolling the loop, we find that this does the correct thing:

    (x_5, x_5') = loop (acc = x_4 * x_4, acc' = x_4' * x_4 + x_4 + x_4') for i < 1 do
                    (acc * x_4, acc' * x_4 + acc * x_4')

                = (x_4 * x_4 * x_4, (x_4' * x_4 + x_4 * x_4') * x_4 + (x_4 * x_4) * x_4')

To yield the derivative with respect to `x_4`, we set `x_4' = 1`:

    (x_5, x_5') = (x_4 * x_4 * x_4, (x_4 + x_4) * x_4 + (x_4 * x_4))

                = (x_4 * x_4 * x_4, 3 * (x_4 * x_4))

In some sense the above is still "just" reverse-mode: we just use forward-mode to compute the
derivative of the RHS of a statement instead of specifying it directly.

The situation becomes somewhat more complicated when the loop depends on multiple variables:

    x_5 = loop acc = x_2 * x_4 for i < 1 do  -- computes (x_2 * x_4)^2
            acc * (x_2 * x_4)

Forward-mode now yields an expression that is a function of multiple gradients:

    (x_5, x_5') = loop (acc = x_2 * x_4, acc' = x_2' * x_4 + x_2 * x_4') for i < 1 do
                      (acc * (x_2 * x_4), acc' * (x_2 * x_4) + acc * (x_2' * x_4 + x_2 * x_4'))

                = ((x_2 * x_4) * (x_2 * x_4),  (x_2' * x_4 + x_2 * x_4') * (x_2 * x_4) + (x_2 * x_4) * (x_2' * x_4 + x_2 * x_4'))

                = ((x_2 * x_4) * (x_2 * x_4),  2 * (x_2 * x_4) * (x_2' * x_4 + x_2 * x_4'))

Now, for example,

    bar(x_2) = bar(x_3) * x_1 + bar(x_5) * dx_5/dx_2

where where `dx_5/dx_2` is retrieved from the above expression by setting `(x_2', x_4') = (1, 0)`.

#### Vector loops

If a loop returns more than one value, e.g.,

    (x_8,x_9) = loop (accl, accr) = (x_3, x_4) for i < 2 do
	              (x_3 * accl, x_4 * accr)

then the adjoints of `x_3` and `x_4` will have expressions with both `x_8` and `x_9`. Specifically:

    bar(x_3) += bar(x_8) dx_8/dx_3 + bar(x_9) dx_9/dx_3
	
and similarly for `x_4`.

## General approach

# Efficient computation

## Inner-product

When we take forward-mode derivatives of functions `f: R^n -> R^m`, we
must specify the direction in which we're taking the derivative by
choosing an appropriate vector of gradient variables, i.e. the vector

    (x_0', x_2', ..., x_{n-1}')

where each component, in essence, represents the weighting of change
in its respective component that we're interested in. This often
reduces to a one-hot vector where we're only interested in the
derivative with respect to a single component

    (x_0' = 0, x_2' = 0, ..., x_i' = 1, .., x_{n-1}' = 0)

If we naively apply forward mode to the inner product `b^T x`, we obtain

    (b^T x)' = (b_0 x_0 + ... + b_{n-1} x_{n-1})'
	         = b_0 x_0' + ... + b_{n-1} x_{n-1}'
			 = reduce (+) 0 (zipWith (*) b x')
		 
However, if the compiler is aware that `x'` is one-hot (with `x_i' = 1`), we can immediately simplify
the above to
 
    (b^T x) = b_i x_i'

### Reductions

#### (*) operator

Derivatives of reductions using the `(*)` operator can be straightfowardly derived via `(*')` where

    x *' y = x' * y + x * y'
	
Reduce operators in Futhark must a) be associative and b) have a neutral element. Associativity:

    (x *' y) *' z = (x' * y + x * y') *' z 
	              = (x' * y + x * y')' * z + (x' * y + x * y') * z'
                  = (x' *' y) * z + (x *' y') * z + (x' * y) * z' + (x * y') * z'
				  
	x *' (y *' z) = x *' (y' * z + z * y')
	              = x' * (y' * z + z * y') + x * (y' * z + z * y')'
	
## Peng-Robinson equation (Fig 5., Automatic Differentiation in Machine Learning: a Survey (Baydin))

[Paper here.](https://arxiv.org/pdf/1502.05767.pdf)

We wish to differentiate

![f(x) = \sum_{j=0}^n \log \frac{x_j}{1 - \mathbf{b}^T \mathbf{x}} - \frac{\mathbf{x}^T \mathbf{A} \mathbf{x}}{\mathbf{b}^T \mathbf{x}} \log \frac{1  + \mathbf{b}^T \mathbf{x}}{1 - \mathbf{b}^T \mathbf{x}}](https://render.githubusercontent.com/render/math?math=f(x)%20%3D%20%5Csum_%7Bj%3D0%7D%5En%20%5Clog%20%5Cfrac%7Bx_j%7D%7B1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%20-%20%5Cfrac%7B%5Cmathbf%7Bx%7D%5ET%20%5Cmathbf%7BA%7D%20%5Cmathbf%7Bx%7D%7D%7B%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%20%5Clog%20%5Cfrac%7B1%20%20%2B%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%7B1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D)

Taking the derivative of the sum, we obtain

![\left( \sum_{j=0}^n \log \frac{x_j}{1 - \mathbf{b}^T \mathbf{x}} \right)' = \sum_{j=0}^n \frac{1 - \mathbf{b}^T \mathbf{x}}{x_j} \left( \frac{x_j' \cdot  (1 - \mathbf{b}^T \mathbf{x}) - x_j \cdot (1-\mathbf{b}^T \mathbf{x})'}{(1 - \mathbf{b}^T \mathbf{x})^2}\right)'](https://render.githubusercontent.com/render/math?math=%5Cleft(%20%5Csum_%7Bj%3D0%7D%5En%20%5Clog%20%5Cfrac%7Bx_j%7D%7B1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%20%5Cright)'%20%3D%20%5Csum_%7Bj%3D0%7D%5En%20%5Cfrac%7B1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%7Bx_j%7D%20%5Cleft(%20%5Cfrac%7Bx_j'%20%5Ccdot%20%20(1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D)%20-%20x_j%20%5Ccdot%20(1-%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D)'%7D%7B(1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D)%5E2%7D%5Cright)')

which can be thought of as a map over `zip x x'` which computes the summand for each `j`, followed by a reduce to compute the actual sum.

If we encorporate what we know about `x'`--namely that it's one-hot with `x_i' = 1`--we have

![x_j' \cdot  (1 - \mathbf{b}^T \mathbf{x}) - x_j \cdot (1-\mathbf{b}^T \mathbf{x})' = x_j' \cdot (1 - \mathbf{b}^T \mathbf{x}) + x_j b_i x_i'](https://render.githubusercontent.com/render/math?math=x_j'%20%5Ccdot%20%20(1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D)%20-%20x_j%20%5Ccdot%20(1-%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D)'%20%3D%20x_j'%20%5Ccdot%20(1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D)%20%2B%20x_j%20b_i%20x_i')

for the numerator. Ignoring the constant factors, we have something of the form

![\sum_{j=0}^n \frac{x_j' + x_jb_ix_i'}{x_j}](https://render.githubusercontent.com/render/math?math=%5Csum_%7Bj%3D0%7D%5En%20%5Cfrac%7Bx_j'%20%2B%20x_jb_ix_i'%7D%7Bx_j%7D)


For the second part of the equation

![\frac{\mathbf{x}^T \mathbf{A} \mathbf{x}}{\mathbf{b}^T \mathbf{x}} \log \frac{1  + \mathbf{b}^T \mathbf{x}}{1 - \mathbf{b}^T \mathbf{x}}](https://render.githubusercontent.com/render/math?math=%20%5Cfrac%7B%5Cmathbf%7Bx%7D%5ET%20%5Cmathbf%7BA%7D%20%5Cmathbf%7Bx%7D%7D%7B%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%20%5Clog%20%5Cfrac%7B1%20%20%2B%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%7B1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D)

let's look at computing `x^T A x`.

    x^T A = map (sum . zipWith (*) x) A
	
	x^T A x = sum . zipWith (*) (x^T A) x = sum . zipWith (*) (map (sum . zipWith (*) x) A) x
	
To illustrate, let's look at the case where `A` is a `2x2` matrix:

    A = [[a_00, a_01], [a_10, a_11]]
	
Then

    x^T A = map (sum . zipWith (*) x) A 
	      = [(sum . zipWith (*) x) [a_00, a_01], (sum.  zipWith (*) x) [a_10, a_11]]
		  = [ x_0 * a_00 + x_1 * a_01, x_0 * a_10 + x_1 * a_11]
		  
    x^T A x = sum . zipWith (*) (x^T A) x 
	      = x_0 * (x_0 * a_00 + x_1 * a_01) +  x_1 * (x_0 * a_10 + x_1 * a_11)
		  
For the derivatives,

    (x^T A)' = map (sum . zipWith (*') x) A 
	         = [(sum . zipWith (*') x) [a_00, a_01], (sum.  zipWith (*') x) [a_10, a_11]]
		     = [ x_0 *' a_00 + x_1 *' a_01, x_0 *' a_10 + x_1 *' a_11]
		     = [ x_0' * a_00 + x_1' * a_01, x_0' * a_10 + x_1' * a_11]
			 
    (x^T A x) = sum . zipWith (*') (x^T A) x
	          = (x_0 *' (x_0 * a_00 + x_1 * a_01) +  x_1 *' (x_0 * a_10 + x_1 * a_11))
	          = (x_0' * (x_0 * a_00 + x_1 * a_01) + x_0 * (x_0 * a_00 + x_1 * a_01)' +  x_1' * (x_0 * a_10 + x_1 * a_11) + x_1 * (x_0 * a_10 + x_1 * a_11)')
	          = (x_0' * (x_0 * a_00 + x_1 * a_01) + x_0 * (x_0 *' a_00 + x_1 *' a_01) +  x_1' * (x_0 * a_10 + x_1 * a_11) + x_1 * (x_0 *' a_10 + x_1 *' a_11))
			  
where

    x *' y = x' * y + x * y'

If x' is one-hot (say `x_0' = 1`), then

    (x^T A)' = [a_00, a_10]
	
    (x^T A x)' = sum . zipWith (*') (x^T A) x
	           = x_0' * (x_0 * a_00 + x_1 * a_01) + x_0 * (x_0 *' a_00 + x_1 *' a_01) +  x_1' * (x_0 * a_10 + x_1 * a_11) + x_1 * (x_0 *' a_10 + x_1 *' a_11)
	           = (x_0 * a_00 + x_1 * a_01) + x_0 * (x_0 *' a_00 + x_1 *' a_01) + x_1 * (x_0 *' a_10 + x_1 *' a_11)
	           = (x_0 * a_00 + x_1 * a_01) + x_0 * a_00  + x_1 * a_10 

## Taking derivatives of SOACS/compositions of SOACS

