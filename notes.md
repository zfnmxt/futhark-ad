# Mixed-mode:

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
form x_l = f(x_{r, 0}, x_{r_1}, ..., x_{r,n}) we insert n adjoint
variables bar(x_{r,i}) into a map associating normal variables with
their adjoints:

   bar(x_{r,i}) += dx_6/d(x_{r,i}) = bar(x_l) dx_l/d(x_{r,i})

This is easy to do for statements like `x_3 = x_1 * x_2` since

   bar(x_1) = bar(x_3) dx_3/dx_1 = bar(x_3) x_2

But it's not straight-forward how to compute bar(x_4) since the
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

## General approach

# Efficient computation

## Inner-product

When we take forward-mode derivatives of functions `f: R^n -> R^m`, we
must specify the direction in which we're taking the derivative by
choosing an appropriate vector of gradient variables, i.e. the vector

    (x_1', x_2', ..., x_n')

where each component, in essence, represents the weighting of change
in its respective component that we're interested in. This often
reduces to a one-hot vector where we're only interested in the
derivative with respect to a single component

    (x_1' = 0, x_2' = 0, ..., x_i' = 1, .., x_n' = 0)

If we naively apply forward mode to the inner product `b^T x`, we obtain

    (b^T x)' = (b_1 x_1 + ... + b_n x_n)'
	         = b_1 x_1' + ... + b_n x_n'
			 = reduce (+) 0 (zipWith (*) b x')
		 
However, if the compiler is aware that `x'` is one-hot (with `x_i' = 1`), we can immediately simplify
the above to
 
    (b^T x) = b_i x_i'
	
### Peng-Robinson equation (Fig 5., Automatic Differentiation in Machine Learning: a Survey (Baydin))

![f(x) = \sum_{i=0}^n \log \frac{x_i}{1 - \mathbf{b}^T \mathbf{x}} - \frac{\mathbf{x}^T \mathbf{A} \mathbf{x}}{\mathbf{b}^T \mathbf{x}} \log \frac{1  + \mathbf{b}^T \mathbf{x}}{1 - \mathbf{b}^T \mathbf{x}}](https://render.githubusercontent.com/render/math?math=f(x)%20%3D%20%5Csum_%7Bi%3D0%7D%5En%20%5Clog%20%5Cfrac%7Bx_i%7D%7B1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%20-%20%5Cfrac%7B%5Cmathbf%7Bx%7D%5ET%20%5Cmathbf%7BA%7D%20%5Cmathbf%7Bx%7D%7D%7B%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%20%5Clog%20%5Cfrac%7B1%20%20%2B%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D%7B1%20-%20%5Cmathbf%7Bb%7D%5ET%20%5Cmathbf%7Bx%7D%7D)

