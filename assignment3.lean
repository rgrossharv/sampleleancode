import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option warningAsError false
/-
FIRST EXERCISE: Strict monotonicity

Section 3.1 of MIL discusses the `monotone` predicate. There is also a strict
version. Prove the theorems below, *and* come up with suitable names
(in other words, replace `example` with `theorem foo`.)

(Don't use any library theorems about `strict_mono` or `monotone`! You should
only use basic properties of orderings.)
-/

#print Monotone
#print StrictMono

namespace strict_mono_exercise

variable (f : ℝ → ℝ) (g : ℝ → ℝ)

example (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f + g) := by
  intros a b
  intro h
  apply add_lt_add
  · exact hf h
  exact hg h

/-Here^ I merely introduce the hypothesis, apply the relevant way to break this apart
Then, I use the hypotheses hf and hg accordingly to close the proof.-/

-- You'll have to guess at the name of a theorem for this one.
example (c : ℝ) (hf : StrictMono f) (hc : 0 < c) :
  StrictMono (fun x ↦ c * f x) := by
  intros a b
  intro h
  have h1 : f a < f b := by
    exact hf h
  exact mul_lt_mul_of_pos_left h1 hc

/- Since we had to `guess` I used exact? and it managed to close the proof.
   My understanding is that the.mpr just uses the reverse direction of this iff statement
   The iff statement does indeed make sense, since it merely is saying a < b → c * a < c * b
   given our hypothesis -/

-- This is trickier than you might think. Use `by_cases h : a = b` to split
-- on cases whether `a = b`. You can also use `lt_of_le_of_ne`.

theorem foo (hf : StrictMono f) : Monotone f := by
  intros a b
  intro h
  by_cases h2 : a = b
  · rw [h2]
  have lt : a < b := by
    exact lt_of_le_of_ne h h2
  have ltf : f a < f b := by
    apply hf lt
  exact le_of_lt ltf

/-
The following (trivial) example shows how to use trichotomy. You do not need
to fully understand the pattern now; you can take it as a black box.
-/

example (x1 x2 : ℝ) : x1 ≤ x2 ∨ x2 < x1 := by
  rcases lt_trichotomy x1 x2 with h | h | h
  { -- In this case, we have `h : x1 < x2`.
    left
    apply le_of_lt h }
  { -- In this case, we have `h : x1 = x2`.
    left
    rw [h] }
  -- In this case, we have `h : x2 < x1`
  right
  exact h

-- another example

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

open Function

/-
Here is an example that shows that `x ↦ x + 1` is injective.
-/

example : Injective (fun x ↦ x + 1) := by
  intros x1 x2 h
  dsimp at h -- this makes `h` more readable
  exact add_right_cancel h


/-
Show that every strictly monotone function is injective.
-/

theorem injective_of_strict_mono (hf : StrictMono f) : Injective f := by
  intros a b h
  rcases lt_trichotomy a b with h1 | h2 | h3
  swap
  · exact h2
  · have con1 : f a ≠ f b := by
      have ineq1 : f a < f b := by
        exact hf h1
      exact ne_of_lt ineq1
    contradiction
  · have con2 : f a ≠ f b := by
      have ineq2 : f b < f a := by
        exact hf h3
      exact ne_of_gt ineq2
    contradiction

/- Sorry for the nested have statements this took a while
    Basically I fought to find those little ne_of_lt and
    ne_of_gt functions which finally gave me some closes
    It also took a second to find the contradiction structure
    Like to me having a < b clealy tells me that a ≠ b
    See a refined theorem below -/

end strict_mono_exercise

/-
SECOND EXERCISE: Galois connections

Given `α` with a partial order, a *closure operator* `cl : α → α` has the
following properties:

- `cl` is monotone
- `cl` is increasing, in the sense that for every `a : α`, `a ≤ cl a`
- `cl` is idempotent, in the sense that for every `a : α`, `cl (cl a) = cl a`.

Given `α` and `β` with partial orders, a *Galois connection* is a pair of
monotone functions `f : α → β` and `g : β → α` satisfying the following:

  For every `a` and `b`, `f a ≤ b` if and only if `a ≤ g b`.

You can read more about these here:

  https://en.wikipedia.org/wiki/Closure_operator
  https://en.wikipedia.org/wiki/Galois_connection

The exercises below ask you to show that if `f` and `g` form a Galois
connection, then `g ∘ f` is a closure operator, and `f ∘ g` is a closure
operator on the reverse order.
-/

namespace galois_connection_exercise

variable {α β : Type*} [PartialOrder α] [PartialOrder β]
variable {f : α → β}
variable {g : β → α}
variable {mono_f : Monotone f}
variable {mono_g : Monotone g}
variable {adj1 : ∀ a b, f a ≤ b → a ≤ g b}
variable {adj2 : ∀ a b, a ≤ g b → f a ≤ b}

section
-- you can use these:
include mono_f mono_g

theorem mono_gf : Monotone (g ∘ f) := by
  intros a b h
  have h1 : f a ≤ f b := by
    exact mono_f h
  exact mono_g h1

theorem mono_fg : Monotone (f ∘ g) := by
  intros a b h
  have h1 : g a ≤ g b := by
    exact mono_g h
  exact mono_f h1

end

section
include adj1

theorem increasing_gf : ∀ a, a ≤ g (f a) := by
  intro a
  apply adj1
  rfl

end

section
include adj2

theorem decreasing_fg : ∀ b, f (g b) ≤ b := by
  intro b
  apply adj2
  rfl

end


include mono_f mono_g adj1 adj2
-- For some reason I had to delete mono_g since
-- it was not included in the relevant theorem

#check mono_f
#check mono_fg
#check mono_fg
#check mono_gf
#check increasing_gf
#check decreasing_fg

theorem idempotent_gf : ∀ a, g (f (g (f a))) = g (f a) := by
  intro a
  have increasing_gf' : a ≤ g (f a) := by
    apply adj1
    rfl
  have decreasing_fg' : f (g (f a)) ≤ f a := by
    apply adj2
    rfl
  have h1 : f a ≤ f (g (f a)) := by
    apply mono_f
    apply increasing_gf'
  have h2 : f a = f (g (f a)) := by
    apply le_antisymm h1 decreasing_fg'
  rw [← h2]

--So removing mono_g got rid of the squiggly in the first one
--We replace mono_f for the opposite proof for the same reason
--Lean said it was just that it wasn't used that gave it the
--Yellow squiggly, thus I still believe my proofs to be right
--In fact, they just need less than what Prof. Wood gave me


theorem idempotent_fg : ∀ b, f (g (f (g b))) = f (g b) := by
  intro b
  have decreasing_fg'' : f (g b) ≤ b := by
    apply adj2
    rfl
  have increasing_gf'' : g b ≤ g (f (g b)) := by
    apply adj1
    rfl
  have h1 : g (f (g b)) ≤ g b := by
    apply mono_g
    apply decreasing_fg''
  have h2 : g b = g (f (g b)) := by
    apply le_antisymm increasing_gf'' h1
  rw [← h2]

-- I think this is just an error, since when I use the example
-- Version of each statement the type checking goes through fine
-- idempotent_gf
example : ∀ a, g (f (g (f a))) = g (f a) := by
  intro a
  have increasing_gf' : a ≤ g (f a) := by
    apply adj1
    rfl
  have decreasing_fg' : f (g (f a)) ≤ f a := by
    apply adj2
    rfl
  have h1 : f a ≤ f (g (f a)) := by
    apply mono_f
    apply increasing_gf'
  have h2 : f a = f (g (f a)) := by
    apply le_antisymm h1 decreasing_fg'
  rw [← h2]

-- idempotent_fg
example : ∀ b, f (g (f (g b))) = f (g b) := by
  intro b
  have decreasing_fg'' : f (g b) ≤ b := by
    apply adj2
    rfl
  have increasing_gf'' : g b ≤ g (f (g b)) := by
    apply adj1
    rfl
  have h1 : g (f (g b)) ≤ g b := by
    apply mono_g
    apply decreasing_fg''
  have h2 : g b = g (f (g b)) := by
    apply le_antisymm increasing_gf'' h1
  rw [← h2]

end galois_connection_exercise

/-
THIRD EXERCISE: convergence to infinity

Below, `to_infinity f` expresses that `f x` approaches infinity as
`x` approaches infinity.

The properties below are analogous to properties proved in Sections 3.2
and 3.6 in Mathematics in Lean. They involve the universal and existential
quantifiers (both no other logical connectives).
-/

def to_infinity (f : ℝ → ℝ) := ∀ b, ∃ x₀, ∀ x, x₀ ≤ x → b < f x

-- hint: you can use `linarith` at the end
example (f : ℝ → ℝ) (r : ℝ) (hf : to_infinity f) :
  to_infinity (fun x ↦ f x  + r) := by
  unfold to_infinity at hf
  unfold to_infinity
  dsimp
  intro b
  have h1 : ∃ x₀, ∀ (x : ℝ), x₀ ≤ x → b-r < f x := by
    apply hf
  rcases h1 with ⟨a, hfa⟩
  use a
  intros x h
  apply lt_add_of_tsub_lt_right --finding this is just super hard
  apply hfa
  exact h


-- hint: `div_lt_iff'` is useful here
example (f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hf : to_infinity f) :
  to_infinity (fun x ↦ r * f x) := by
  unfold to_infinity
  unfold to_infinity at hf
  dsimp
  intro b
  have h1 : ∃ x₀, ∀ (x : ℝ), x₀ ≤ x → b/r < f x := by
    apply hf
  rcases h1 with ⟨a, hfa⟩
  use a
  intros x h
  exact (div_lt_iff₀' hr).mp (hfa x h)


#check le_max_left

-- hint: you can use `le_max_left` and `le_max_right`
example (f g : ℝ → ℝ) (hf : to_infinity f) (hg : to_infinity g) :
  to_infinity (f + g) := by
  unfold to_infinity
  unfold to_infinity at hf
  unfold to_infinity at hg
  dsimp
  intro b
  have hf1 : ∃ x₀, ∀ (x : ℝ), x₀ ≤ x → b/2 < f x := by
    apply hf
  have hg1 : ∃ x₀, ∀ (x : ℝ), x₀ ≤ x → b/2 < g x := by
    apply hg
  rcases hf1 with ⟨a₁, hf1a⟩
  rcases hg1 with ⟨a₂, hg1a⟩
  use max a₁ a₂
  intros x h
  have ha1 : a₁ ≤ x  := by
    exact le_of_max_le_left h
  have ha2 : a₂ ≤ x := by
    exact le_of_max_le_right h
  specialize hf1a x ha1
  specialize hg1a x ha2
  have really? : b < f x + g x := by
    linarith
  exact really?
