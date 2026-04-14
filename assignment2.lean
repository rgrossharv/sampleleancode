import Mathlib.Analysis.InnerProductSpace.PiL2
--import Mathlib.Analysis.InnerProductSpace.Basic

/-
This assignment is due midnight on Friday, February 6, 2026

Copy this file to `assignment2/assignment2.lean` in your personal `har-ifvm-23-{username}`
directory, and fill in the proofs. When you are done, push it to Github:
```
  git add assignment2.lean
  git commit -m "my assignment2 solutions"
  git push
```
Feel free to push any preliminary commits.
-/

/-
FIRST EXERCISE: the parallelogram law
-/

namespace parallelogram_exercise
open scoped RealInnerProductSpace

/-
In the following variable declaration, `euclidean_space ℝ (fin 2)` represents
the Euclidean plane, ℝ × ℝ, with the usual definition of inner product.
-/

variable {x y z : EuclideanSpace ℝ (Fin 2)}

#check ⟪x, y⟫    -- the inner product
#check ‖x‖       -- the norm
#check x + y
#check 3 • x

/-
Hovering over the brackets in VS Code shows that the angle brackets for the inner product can be
written as `\<<` and `\>>`, and the bars for the norm can be written `\||`.

They satisfy the following identities:
-/

#check inner_add_right

example : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := inner_add_right _ _ _
example : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := inner_add_left _ _ _
example : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := inner_sub_right _ _ _
example : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := inner_sub_left _ _ _

-- In the above, note that sometimes you need to add the underscore _ as a
-- blank for Lean to fill in.  Do the examples above typecheck without the underscores?



-- *************************************************************************
-- Solution: The example statements are listed below without the underscores,

example : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := inner_add_right
example : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := inner_add_left
example : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := inner_sub_right
example : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := inner_sub_left

-- You will notice (if your lean is running as mine is) the little red squigglys
-- Moreover, there are no double check marks to tell us our proof is complete and the infoview has goals for each one
-- *************************************************************************

example :  ⟪x, x⟫ = ‖x‖^2 := real_inner_self_eq_norm_sq x
-- Does the example above typecheck without the x?  What about with a _ ?
-- *************************************************************************
-- Solution: Below I have written the example statement without the x (nothing following it)
-- and I have written the statement with a subscript

example :  ⟪x, x⟫ = ‖x‖^2 := real_inner_self_eq_norm_sq
example :  ⟪x, x⟫ = ‖x‖^2 := real_inner_self_eq_norm_sq _

-- We can see that the first example statement with no x checked is not sufficient to typecheck
-- However, we have our second example statement with the subscript that does indeed typecheck.
-- *************************************************************************

/-
The following identity is known as the *parallelogram law*. It says that the sum of the squares
of the lengths of the four sides of a parallegram is equal to the sum of the squares of the
lengths of the diagonals.

You can read a proof of it on Wikipedia: https://en.wikipedia.org/wiki/Parallelogram_law.

Formalize it using only the five identities above as well as the `ring` tactic.
-/

example :
  ‖x + y‖^2 + ‖x - y‖^2  = 2 * (‖x‖^2 + ‖y‖^2) := by
  have h1 : ⟪x+y,x+y⟫ = ‖x+y‖^2 := by apply real_inner_self_eq_norm_sq
  have h2 : ⟪x-y,x-y⟫ = ‖x-y‖^2 := by apply real_inner_self_eq_norm_sq
  rw [← h1, ← h2, inner_add_left, inner_add_right, inner_add_right]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, ← real_inner_self_eq_norm_sq]
  rw [← real_inner_self_eq_norm_sq]
  ring
/-

-- ***************************************************************************************

Here, I have some comments on what I've done for my proof. First, I wanted to make sure we
could get rid of the norms, hence I have my ``have'' statements which manage to get us into
the vector forms of each one. Finally, I do some rewrites using these new hypotheses and ]
the earlier statements to break it all up into stuff like ⟪a,b⟫ where I can use ring to eliminate
like terms, then I bring it back to the real versions with the norm statement and this completes
the proof.

-- ***************************************************************************************

In fact, the theorem holds for arbitrary inner product spaces, with exactly the same proof.
You can check this by replacing the variable declaration above by the following:

variables {E : Type*} [inner_product_space ℝ E]
variables x y z : E
-/

end parallelogram_exercise

/-
SECOND EXERCISE: Boolean rings
-/

namespace boolean_ring_exercise

/-
The notion of a ring is discussed in the textbook:
https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#proving-identities-in-algebraic-structures

A *Boolean* ring satisfies the additional property that for every `x`, `x^2 = x`.
You can read about Boolean rings here:
https://en.wikipedia.org/wiki/Boolean_ring
-/

variable {R : Type*} [Ring R]

-- This is the assumption that makes `R` a Boolean ring:
variable (idem : ∀ x : R, x ^ 2 = x)

-- This adds `idem` as a hypothesis to every theorem:
include idem

/-
This exercise asks you to prove that every Boolean ring is commutative, i.e.
satisfies `x * y = y * x` for every `x` and `y`. Unfortunately, we cannot use the
`ring` tactic along the way, since it only works once we know a ring is commutative.
So you will have to rely on theorems like `mul_add`, `add_mul`, etc. in the textbook.
-/

-- This is useful:
theorem mul_idem (x : R) : x * x = x :=
by rw [←pow_two, idem]

-- Unfortunately, you have to write `mul_idem idem` to use it.
example (x y : R) : (x + y) * (x + y) = x + y :=
by rw [mul_idem idem]

/-
Prove the following theorem, following the calculation in Wikipedia:
x + x = (x+x)^2 = x^2 + x^2 + x^2 + x^2 = (x + x) + (x + x).
-/

theorem add_self (x : R) : x + x = 0 := by
  have h1 : x + x = (x + x) + (x + x) :=
  calc
    x + x = (x + x)^2 := by
      rw [idem]
    _ = x + x + (x + x) := by
      rw [pow_two, mul_add, add_mul]
      rw [← add_assoc, ← add_assoc]
      rw [mul_idem idem]
  have h2 : (x + x) + (x + x) - (x + x) = (x + x) - (x + x) := by
     rw [←h1]
  rw [add_sub_cancel_right, sub_self] at h2
  exact h2

/-
***************************************************************************
So, here I have really just played around with some of the functions in the relevant
textbook chapter. I found that mul_add and add_mul would help me distribute everything
and this was very useful. Then using \l add_assoc got rid of the parentheses which made
everything much easier. All the difficulty here was just figuring out (x+x) * (x+x) =
x^2 + x^2 + x + x and then making sure lean didn't have problems with the parent
***************************************************************************
-/

-- Note: again, to use this theorem you have to mention `idem` explicitly
example (y : R) : y + y = 0 :=
add_self idem y

/-
Prove `neg_eq_self` using the calculation `-x = 0 - x = x + x - x = x`. You can use the theorems
`zero_sub` and `add_sub_cancel`, as well as `add_self idem`.
-/

#check add_sub_cancel

theorem neg_eq_self (x : R) : -x = x := by
  calc
    -x = 0-x := by
      rw [← zero_sub]
    _ = x + x - x := by
      rw [add_self idem x]
    _ = x := by
      rw [add_sub_cancel_right]

/-
****************************************************************************
Here we just rewrite and add the zero_sub, then using add_self idem x we can turn that 0 into x+x
Finally, we use add_sub_cancel_right (from the previous proof) to get rid of one of the x+x-x => x
****************************************************************************
-/

/-
This is a corollary.
-/

theorem sub_eq_add (x y : R) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_self idem]

/-
Prove this, using the calculation `x = x + y - y = 0 - y = -y = y`.
-/
theorem eq_of_add_eq_zero {x y : R} (h : x + y = 0) :
  x = y := by
  calc
    x = x + y - y := by
      rw [add_sub_cancel_right x y]
    _ = 0 - y := by
      rw [h]
    _ = -y := by
      rw [zero_sub]
    _ = y := by
      rw [neg_eq_self idem]

/-
**************************************************************
I feel like the above proof is pretty self explanatory, you just cancel the left side and add zeroes
**************************************************************
-/

/- Finally, prove `mul_comm` using the following argument from Wikipedia:

`0 + x + y = x + y = (x + y)^2 = x^2 + xy + yx + y^2 = xy + yx + x + y`

You can use the `abel` tactic to rearrange sums.
-/

example (x y : R) : x + x * y + y * x + y = x * y + y * x + x + y :=
by abel

theorem mul_comm (x y : R) : x * y = y * x := by
  have h1 : 0 + (x + y) = (x * y + y * x) + (x + y) :=
  calc
    0 + (x + y) = (x + y)^2 :=
      calc
        0 + (x + y) = x + y := by
          rw [zero_add]
        _ = (x + y) * (x + y) := by
          rw [mul_idem idem]
        _ = (x + y)^2 := by
          rw [pow_two]
    _ = x * y + y * x + (x + y) := by
      calc
        (x+y)^2 = (x+y) * (x+y) := by
          rw [pow_two]
        _ = x * x + x * y + y * x + y * y := by
          rw [mul_add, add_mul, add_mul, ← add_assoc]
          abel
        _ = x + y + x * y + y * x := by
          rw [mul_idem idem x, mul_idem idem y]
          abel
        _ = (x * y + y * x) + (x+y) := by
          abel
  have h2 : 0 = x * y + y * x := by
    exact add_right_cancel h1
  change x * y = y * x
  -- post to Ed Discussion if you can figure out why Lean wants `change` here instead of `show`
  -- (or you post if you observe a different behavior here)
  exact eq_of_add_eq_zero idem h2.symm

end boolean_ring_exercise

/-
**************************************************************
This one was much more difficult and I feel like I didn't need to use so many calc statements.
Abel was very helpful, and I'm sorry if this is too nasty to read.
**************************************************************
-/

/-
THIRD EXERCISE: absolute values
-/

namespace absolute_value_exercise

variable {x y z w : ℝ}

/-
Bounding sums often boils down to using transitivity and inequalities. Step through the
next example and make sure you understand what is going on. `swap` switches the order of the goals,
and `norm_num` does a numeric calculation.

The `transitivity` tactic lets you state the intermediate expression. In contrast, applying
`le_trans` lets you make Lean figure it out from context. With the `transitivity` tactic,
we have to specify that the numerals are real numbers, because otherwise Lean assumes that they
are natural numbers.
-/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
  abs (x + y + z) ≤ 19 := by
    transitivity ((10 : ℝ) + 5 + 4)
    swap
    · norm_num
    apply le_trans
    · apply abs_add_le
    -- see alternate path from here on in the example below
    apply add_le_add
    { -- first goal
      apply le_trans
      · apply abs_add_le
      exact add_le_add hx hy }
    -- second goal
    exact hz


/-
We can finish the second goal earlier by giving `hz` right away.
-/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
  abs (x + y + z) ≤ 19 := by
    transitivity ((10 : ℝ) + 5 + 4)
    swap
    · norm_num
    apply le_trans
    · apply abs_add_le
  -- the underscore means: figure it out or leave it as another goal
    apply add_le_add _ hz
    apply le_trans
    · apply abs_add_le
    exact add_le_add hx hy

/-
Prove the following. You can also use the theorems `abs_sub`, `pow_two` to expand `w^2` to `w * w`,
`sq_abs`, and `mul_le_mul`. For the last theorem, you'll need to know that an absolute value is
nonnegative, which is the theorem `abs_nonneg`. You can also use `norm_num` to show that
`(9 : ℝ) = 3 * 3`.
-/

/-
We add Prof. Wood's sample theorem below, modified for relevant details (it was used in
the relevant part of the proof below which is the example statement.)
-/

theorem modifiedwoodproof
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
  abs (x - y + z) ≤ 19 := by
    transitivity ((10 : ℝ) + 5 + 4)
    swap
    · norm_num
    apply le_trans
    · apply abs_add_le
    apply add_le_add _ hz
    apply le_trans
    · apply abs_add_le
    have hy1 : abs (-y) = abs y := by
      apply abs_neg y
      /- ^Took a second to find this playing around with abs_ and looking through the dropdown -/
    have hy2 : abs (-y) ≤ 5 := by
      rw [hy1]
      apply hy
    exact add_le_add hx hy2

/- Here is precisely the proof that was requested -/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4)
    (hw : abs w ≤ 3) :
  abs (x - y + z) + w^2 ≤ 28 := by
  transitivity (10 + 5 + 4 + 9)
  swap
  ·norm_num
  have h1a : abs (x-y+z) ≤ 19 := by
    apply modifiedwoodproof hx hy hz
  have h1b : abs (x-y+z) ≤ 10+5+4 := by
    apply le_trans h1a
    norm_num
  have h1c : |w|^2 = w ^ 2 := by
    exact sq_abs w
  have h2lemma1 : 0 ≤ abs w := by
    exact abs_nonneg w
  have h2lemma2 : (0:ℝ) ≤ 3 := by
    norm_num
  have h2a : w ^ 2 ≤ 3*3 := by
     rw[← h1c, pow_two]
     apply mul_le_mul hw hw h2lemma1 h2lemma2
  have h2b : w ^ 2 ≤ 9 := by
    apply le_trans h2a
    norm_num
  /-This w^2 term is giving me a lot of trouble, so I have made a large number of haves-/
  apply add_le_add _ h2b
  exact h1b

end absolute_value_exercise
