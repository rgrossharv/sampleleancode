import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option warningAsError false
/-
EXERCISE 1. [30pts]

Prove the following without using automation, i.e. only with basic tactics
such as `intros`, `apply`, `split`, `cases`, `left`, `right`, and `use`.
-/

section

variable {α β : Type} (p q : α → Prop) (r : α → β → Prop)

-- Exercise 1a. [10pts]
example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x := by
    intro h
    cases' h with h1 h2
    intro x
    have h11 : p x := by
      exact h1 x
    have h22 : q x := by
      exact h2 x
    constructor
    exact h11
    exact h22

-- The one above is my first pass, the second one came from reading more of the book.

example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x := by
  intros h x
  constructor
  · exact h.left x
  exact h.right x

-- Exercise 1b. [10pts]
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intros h x
  cases' h with h1 h2
  constructor
  · exact h1 x
  right
  exact h2 x

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intros h x
  rcases h with h1 | h2
  · left
    exact h1 x
  right
  exact h2 x

-- First version also before reading textbook

-- Exercise 1c. [10pts]
example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y := by
  intros h y
  rcases h with ⟨x, h11⟩
  use x
  exact h11 y

end

/-
EXERCISE 2.

Suppose two pairs of real numbers {a, b} and {c, d} have the same sum
and product. The following theorem shows that either a = c and b = d,
or a = d and b = c. Fill in the details. You can use `ring`, `ring_nf`
and `linarith` freely.
-/

-- Exercise 2. [20pts]
theorem sum_product_magic (a b c d : ℝ)
    (sumeq : a + b = c + d) (prodeq : a * b = c * d) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have : (a - c) * (a - d) = 0
  { sorry }
  have := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with  h | h
  { sorry }
  { sorry }

-- I hate the syntax used here so I'm rewriting it
theorem sum_product_magic1 (a b c d : ℝ)
    (sumeq : a + b = c + d) (prodeq : a * b = c * d) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have aeq : a = c + d - b := by
    linarith[sumeq]
  have h1 : (a - c) * (a - d) = 0 := by
    ring_nf
    rw[← prodeq]
    rw[aeq]
    ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with  h | h
  · left
    constructor
    · linarith
    linarith
  right
  constructor
  · linarith
  linarith

/-
EXERCISE 3. [30pts]

The predicate `approaches_at f b a` should be read "f(x) approaches b as x
approaches a", and the predicate `continuous f` says that f is continuous.

Prove the following two theorems.

Note that bounded quantification such as `∀ ε > 0, ..` really means `∀ ε, ε > 0 → ..`
and `∃ δ > 0, ..` really means `∃ δ, δ > 0 ∧ ..`.
-/

def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

#check add_sub_add_right_eq_sub

-- Exercise 3a. [10pts]
theorem approaches_at_add_right {f : ℝ → ℝ} {a b c : ℝ}
    (hf : approaches_at f b a) :
  approaches_at (fun x ↦ f x + c) (b + c) a := by
  unfold approaches_at
  unfold approaches_at at hf
  dsimp
  intros ε h
  have hf1 := hf ε h
  rcases hf1 with ⟨δ, hf11⟩
  have hf11left := hf11.left
  have hf11right := hf11.right
  use δ
  constructor
  · exact hf11left
  intros x h
  rw[add_sub_add_right_eq_sub]
  exact hf11right x h

--Below is a cleaner version

theorem approaches_at_add_right2 {f : ℝ → ℝ} {a b c : ℝ}
    (hf : approaches_at f b a) :
  approaches_at (fun x ↦ f x + c) (b + c) a := by
  intros ε h
  have hf1 := hf ε h
  rcases hf1 with ⟨δ, hf11⟩
  use δ
  constructor
  · exact hf11.left
  intros x h
  rw[add_sub_add_right_eq_sub]
  exact hf11.right x h

-- Exercise 3b. [10pts]
theorem approaches_at_comp2 {f g : ℝ → ℝ} {a b c : ℝ}
  (hf : approaches_at f b a) (hg : approaches_at g c b) :
    approaches_at (g ∘ f) c a := by
  unfold approaches_at
  unfold approaches_at at hf
  unfold approaches_at at hg
  dsimp
  intros ε h
  have hg1 := hg ε h
  rcases hg1 with ⟨δ, hg1p⟩
  have hf1 := hf δ hg1p.left
  rcases hf1 with ⟨d, hf1p⟩
  use d
  constructor
  · exact hf1p.left
  intros x h2
  have hf1pr := hf1p.right x h2
  exact hg1p.right (f x) hf1pr

--needed to write the below examples to get the exact statements to work

example (a b : ℝ) (h : a > 0) (h2 : b > 0) : min a b > 0 := by
  exact lt_min h h2


def continuous (f : ℝ → ℝ) := ∀ x, approaches_at f (f x) x

-- Exercise 3c. [10pts]
theorem my_continuous_add_right {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (fun x ↦ f x + r) := by
  unfold continuous
  unfold continuous at ctsf
  unfold approaches_at
  unfold approaches_at at ctsf
  intros x ε h
  dsimp
  --as necessary for rcases we need this
  have h1 := ctsf x ε h
  rcases h1 with ⟨δ, h11⟩
  use δ
  constructor
  · exact h11.left
  intros x_1 h
  rw[add_sub_add_right_eq_sub]
  exact h11.right x_1 h

-- Here is a slightly cleaner version of the last theorem

theorem my_continuous_add_right2 {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (fun x ↦ f x + r) := by
  intros x ε h
  have h1 := ctsf x ε h
  rcases h1 with ⟨δ, h11⟩
  use δ
  constructor
  · exact h11.left
  intros x_1 h
  rw[add_sub_add_right_eq_sub]
  exact h11.right x_1 h


-- Since `f x - r` is the same as `f x + (- r)`, the following is an instance
-- of the previous theorem.
theorem continuous_sub {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (fun x ↦ f x - r) :=
  my_continuous_add_right ctsf (-r)

/-
EXERCISE 4.

In class, I will prove the intermediate value theorem in the form `ivt`.
Use that version to prove the more general one that comes after.
-/

/- We'll do this in class! You don't have to prove it,
   and you can leave the `sorry` and apply the theorem
   as a black box. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
sorry

-- Use `ivt` to prove `ivt'` below.

-- Exercise 4. [20pts]
theorem ivt' {f : ℝ → ℝ} {a b c : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < c) (hfb : c < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c := by
  unfold continuous at ctsf
  unfold approaches_at at ctsf
  let g := fun x ↦ f x - c
  have h1 : ∃ x, a ≤ x ∧ x ≤ b ∧ g x = 0 := by
    have ctsg : continuous g := by
      apply continuous_sub ctsf
    apply ivt aleb ctsg
    · linarith [hfa]
    linarith [hfb]
  dsimp [g] at h1
  rcases h1 with ⟨x, h11⟩
  use x
  constructor
  · exact h11.left
  constructor
  · exact h11.right.left
  exact eq_of_sub_eq_zero h11.right.right

example (a c : ℤ) (h : a < c) : a - c < 0 := by
  exact Int.sub_neg_of_lt h

example (a c : ℤ) (h : c < a) : 0 < a - c := by
  exact Int.sub_pos_of_lt h

-- Writing these examples with integers has proven a solid tactic to find specific theorems

-- Without Linarith
theorem ivtnolinarith {f : ℝ → ℝ} {a b c : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < c) (hfb : c < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c := by
  unfold continuous at ctsf
  unfold approaches_at at ctsf
  let g := fun x ↦ f x - c
  have h1 : ∃ x, a ≤ x ∧ x ≤ b ∧ g x = 0 := by
    have ctsg : continuous g := by
      apply continuous_sub ctsf
    apply ivt aleb ctsg
    · exact sub_neg_of_lt hfa
    exact sub_pos_of_lt hfb
  dsimp [g] at h1
  rcases h1 with ⟨x, h11⟩
  use x
  constructor
  · exact h11.left
  constructor
  · exact h11.right.left
  exact eq_of_sub_eq_zero h11.right.right
