# Smith Normal Form Lean 3 Formalisation Project

This is my first project using Lean 3. I attempt to formalise Smith Normal Form as outlined in [Basic Algebra I](http://www.math.toronto.edu/~ila/Jacobson-Basic_algebra_I%20(1).pdf) by Jacobson (Theorem 3.8). This project was done under the supervision of [Prof. Dirk Schuetz](https://www.maths.dur.ac.uk/users/dirk.schuetz/) who was a great help with dissecting the proofs down into managable chunks to formalise.

I used this project to learn Lean and as a consequence, I believe following the implementation in Jacobson, using an algorithm with elementary matrices to show equivalences, is not ideal for Lean. If I was to redo this project, I would not implement elementary matrices, but instead only implement the (equivalence-preserving) maps the elementary matrices induce.

I restricted the theorem for this project to only consider $n \times n$ matrices over Euclidean Domains, although even with this restriction, the SNF result has not been fully implemented. The remaining steps to implement are:
- Implementing the induction argument
- Using well founded relation to show algorithm terminates

Please see below for full details of what remains to implement for the result.

Another possible improvement is to replace some definitions with structures.

## Reading this project

### The Elementary Matrices

I define the following elementary matrices (following definitions in Jacobson):
- `basis` is the basis matrix $\Delta$.
- `add_mult` is the Type I elementary matrix (for adding a multiple of column/row $i$ to $j$).
- `mul_by_unit` is the Type II elementary matrix (for multiplying a row/column by a unit).
- `perm` is the Type III elementary matrix (permutes rows/columns).

I then use the equivalence between `is_unit M` and `is_unit (det M)` to show that the three elementary matrices were invertable (units).

In sections after ("Effect of Permutation Matrix" and "Effect of Add Mult Matrix"), I prove that left/right multiplication by these matrices has the claimed effect. I have not shown the effect of left/right multiplication by `unit_mul` since this is only needed to show that in SNF, the diagonal entries successively divide each other. This could be a future improvement, although, I think an entirely overhauled approach would be better.

### Equivalence of Matrices

I then define a relation on ($m \times n$) matrices (over a Euclidean domain) and show that it is indeed an equivalence relation. `unit_mul` and `mul_unit` then show that left and right multiplication by invertible matrices (units) preserves equivalence.

### SNF

I have then defined what it means for a matrix to be in SNF (under the `snf` definition) and began to setup the machinery for implementing induction argument in the proof.
- `simple_block_diag` defines what it means for a matrix to be block diagonal with the first block being of size $1 \times 1$.
- `is_minimal` defines what it means for an entry in a matrix to have the minimal valuation (in the Euclidean Domain).
- `min_valuation_of_mat` gives the index of the entry of a matrix with minimal valuation.
- `minimal_element_to_00` moves the minimal elemnet to index (0,0) using elementary matrices and hence preserving equivalence.

Note: the implementation of Euclidean Domains in `mathlib` uses a well founded valuation relation instead of a Euclidean function.

`minimal_element_to_00` is over 100 lines long and is generally far longer than it needs to be as the same argument is repeated multiple times for slightly different cases rather than reusing the argument. But I struggled to cut this down and the current proof does compile.

There are then some temporary lemmas aswell as results which still have `sorry`s. `temp1` which doesn't have any `sorry`s shows that if the top left entry of a matrix (with minimal valuation) doesn't divide all the elements in that row and column, then by performing EA, you can obtain an element with lower valuation. It remains to show that this can only be done finitely many times. To do that, The well-founded tactic will need to be used.

## What is Lean?

This project was done in Lean 3 which is an interactive theorem prover, and I used Lean's Maths library [mathslib](https://leanprover-community.github.io/). More information can be found at [LeanProver - About](https://leanprover.github.io/about/).
