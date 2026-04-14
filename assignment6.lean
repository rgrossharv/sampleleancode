import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Init.Internal.Order.Basic

set_option warningAsError false



/- This assignment is due by 11:59pm on Friday, March 3, 2023 . -/

/-
EXERCISE 1.

A function `F : set α → set α` is called a *monotone operator* if for every
pair of sets `s ⊆ t`, we have `F s ⊆ F t`.

Every such operator has a *least fixed point*, i.e. a set `s` satisfying:
- `F s = s`
- For every `t`, if `F t = t`, then `s ⊆ t`.

This exercise has you prove that fact. In fact, the least fixed point is
the intersection of all sets `s` such that `F s ⊆ s`.

This theorem, or the generalization to monotone operators on a complete lattice,
is called *Tarski's theorem* or the *Knaster-Tarski Theorem*. Feel free to use
Google to find more information.
-/
namespace monotone_set_operator
open Set

-- You will need these. The full names are `Set.mem_sInter`, etc.
#check @mem_sInter
#check @subset_sInter
#check @subset_sInter_iff

variable {α : Type*}

def lfp (F : Set α → Set α) := ⋂₀ { t | F t ⊆ t }

variable {F : Set α → Set α}
-- The monotonicity assumption:
variable (monoF : ∀ ⦃s t⦄, s ⊆ t → F s ⊆ F t)



/-
This follows immediately from the definition of `lfp F`.
-/
-- Exercise 1a. [8pts]
theorem aux0 {s : Set α} (h : F s ⊆ s) : lfp F ⊆ s := by
  intros x hx
  have sonesucht : s ∈ {t | F t ⊆ t} := by
    exact mem_setOf.mpr h
  have h2 : Set.sInter {t | F t ⊆ t} ⊆ s := by
    exact sInter_subset_of_mem h
  exact mem_of_subset_of_mem h2 hx

/-
All the remaining theorems in this section need the monotonicity assumption.
After you prove `aux1`, you have to write `aux1 monoF` to use it in a
later theorem.
-/
include monoF

/-
To show this next statement, it suffices to show that `F (lfp F)` is contained
in every set `t` such that `F t ⊆ t`. So suppose `t` has this property.
Then by `aux0`, `lfp F ⊆ t`, and by monotonicity, we have `F (lfp F) ⊆ F t ⊆ t`.
-/
-- Exercise 1b. [10pts]
lemma aux1 : F (lfp F) ⊆ lfp F := by
  unfold lfp
  intro x h
  simp only [mem_sInter, mem_setOf_eq]
  intro t ht
  have h11 : (⋂₀ {t | F t ⊆ t}) ⊆ t := by
    exact sInter_subset_of_mem ht
  exact mem_of_subset_of_mem ht (monoF h11 h)

-- Hint: The remaining exercise 1 proofs below can be done in at most three
-- lines each. (for some reason calling these is not working especially well
-- for me, so I will just rewrite them in the below proofs.)

/- To show this, use `aux0`. -/
-- Exercise 1c. [5pts]
lemma aux2 : lfp F ⊆ F (lfp F) := by
  apply aux0
  intro x h
  have aux1 : F (lfp F) ⊆ lfp F := by
    unfold lfp
    intro x h
    simp only [mem_sInter, mem_setOf_eq]
    intro t ht
    have h11 : (⋂₀ {t | F t ⊆ t}) ⊆ t := by
      exact sInter_subset_of_mem ht
    exact mem_of_subset_of_mem ht (monoF h11 h)
  exact mem_of_subset_of_mem (monoF aux1) h

/- Follows from `aux1` and `aux2`. -/
-- Exercise 1d. [5pts]
theorem lfp_fixed_point : F (lfp F) = lfp F := by
  apply subset_antisymm
  · have aux1 : F (lfp F) ⊆ lfp F := by
      unfold lfp
      intro x h
      simp only [mem_sInter, mem_setOf_eq]
      intro t ht
      have h11 : (⋂₀ {t | F t ⊆ t}) ⊆ t := by
        exact sInter_subset_of_mem ht
      exact mem_of_subset_of_mem ht (monoF h11 h)
    exact aux1
  apply aux0
  intro x h
  have aux1 : F (lfp F) ⊆ lfp F := by
    unfold lfp
    intro x h
    simp only [mem_sInter, mem_setOf_eq]
    intro t ht
    have h11 : (⋂₀ {t | F t ⊆ t}) ⊆ t := by
      exact sInter_subset_of_mem ht
    exact mem_of_subset_of_mem ht (monoF h11 h)
  exact mem_of_subset_of_mem (monoF aux1) h


-- Exercise 1e. [5pts]
theorem lfp_least_fixed_point (s : Set α) (h : F s = s) : lfp F ⊆ s := by
  apply aux0
  exact Eq.subset h

-- will type check as an example

example (s : Set α) (h : F s = s) : lfp F ⊆ s := by
  apply aux0
  exact Eq.subset h

end monotone_set_operator

/-
EXERCISE 2.

A `complete lattice` is a partial order such that every subset has a greatest
lower bound (`Inf`) and a least upper bound (`Sup`). In fact, the existence
of either implies the other.

The proofs above carry over to this more general setting, if you replace
`α` by `set α`, `⊆` by `≤`, `⋂₀` by `Inf`, and make some small adjustments
to the proof.

Really, start by cutting and pasting the proofs above.
-/

namespace monotone_operator
open Order

#check @le_inf
#check @le_inf_iff
#check @inf_le_iff

variable {α : Type*} [CompleteLattice α]

def lfp (F : α → α) := sInf { s | F s ≤ s }

variable {F : α → α} (monoF : ∀ ⦃s t⦄, s ≤ t → F s ≤ F t)

-- Exercise 2a. [5pts]
lemma aux0 {s : α} (h : F s ≤ s) : lfp F ≤ s := by
  unfold lfp
  have sonesucht : s ∈ {s | F s ≤ s} := by
    exact Set.mem_setOf.mpr h
  have h2 : sInf {s | F s ≤ s} ≤ s := by
    exact CompleteSemilatticeInf.sInf_le {s | F s ≤ s} s h
  exact CompleteSemilatticeInf.sInf_le {s | F s ≤ s} s h


include monoF

-- Exercise 2b. [5pts]
lemma aux1 : F (lfp F) ≤ lfp F := by
  unfold lfp
  simp only [le_sInf_iff, Set.mem_setOf_eq]
  intro t ht
  have h11 : (sInf {t | F t ≤ t}) ≤ t := by
    exact CompleteSemilatticeInf.sInf_le {t | F t ≤ t} t ht
  exact Std.IsPreorder.le_trans (F (sInf {s | F s ≤ s})) (F t) t (monoF h11) ht


-- Exercise 2c. [3pts]
lemma aux2 : lfp F ≤ F (lfp F) := by
  apply aux0
  apply monoF
  apply aux1 monoF

-- Exercise 2d. [2pts]
theorem lfp_fixed_point : F (lfp F) = lfp F := by
  have aux1' := aux1 monoF
  have aux2' := aux2 monoF
  exact Std.IsPartialOrder.le_antisymm (F (lfp F)) (lfp F) aux1' aux2'
  -- This just uses the example above which is trivial


-- Exercise 2e. [2pts]
theorem lfp_least_fixed_point (s : α) (h : F s = s) : lfp F ≤ s := by
  apply aux0
  exact ge_of_eq (id (Eq.symm h))

example (s : α) (h : F s = s) : lfp F ≤ s := by --typechecks as example
  apply aux0
  exact ge_of_eq (id (Eq.symm h))

end monotone_operator

/-
EXERCISE 3.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`B n = ⋃ i < n, A i`. Then the sequence `B 0, B 1, B 2, ...` is a monotone
sequence with the same union.
-/

namespace set_sequences

variable {α : Type*}
variable (A B : ℕ → Set α)
variable (B_def : ∀ n, B n = ⋃ i < n, A i)

/-
Remember, a (bounded) union corresponds to a (bounded) existential quantifier.
Use the simplifier with `simp only [Set.mem_iUnion]` to do the translation for
you. You can also write `simp only [Set.mem_iUnion] at h` to simplify a
hypothesis. You can also just use `simp`. However, mathlib conventions
discourage "non-terminal" calls, i.e. ones which don't close a goal, to `simp`
without `only`.
-/
theorem foo (x : α) (n : ℕ) : (x ∈ ⋃ i < n, A i) ↔ ∃ i < n, x ∈ A i :=
  by simp only [Set.mem_iUnion, exists_prop]

-- This might be helpful to you:
example (i : ℕ) : i < i + 1 := Nat.lt_succ_self _

include B_def

-- Exercise 3a. [10pts]
theorem monotone_B : ∀ i j, i ≤ j → B i ⊆ B j := by
  simp only [B_def]
  intro i j h1 x h2
  simp only [Set.mem_iUnion, exists_prop] at h2
  rcases h2 with ⟨a, h2a, h2a1⟩
  simp only [Set.mem_iUnion, exists_prop]
  use a
  constructor
  · exact Nat.lt_of_lt_of_le h2a h1
  exact h2a1

-- Exercise 3b. [15pts]
theorem Union_B_eq_Union_A : (⋃ i, B i) = (⋃ i, A i) := by
  apply subset_antisymm
  . simp only [B_def]
    intro x h
    simp only [Set.mem_iUnion] at h
    rcases h with ⟨n, i, ha2, ha3⟩
    exact Set.mem_iUnion_of_mem i ha3
  intro i h
  simp only [Set.mem_iUnion] at h
  rcases h with ⟨n, hn⟩
  simp only [Set.mem_iUnion]
  use n + 1
  have bl := B_def (n+1)
  simp only [B_def, Set.mem_iUnion]
  use n
  constructor
  · exact hn
  linarith

end set_sequences

/-
EXERCISE 4.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`C n = A n \ (⋃ i < n, A i)`. Then whenever `i ≠ j`, the sets `C i` and `C j` are
disjoint, but the sequence still has the same union.
-/

namespace set_sequences

variable {α : Type*}
variable (A C : ℕ → Set α)
variable (C_def : ∀ n, C n = A n \ (⋃ i < n, A i))

-- This may be useful.
--#check @Set.eq_empty_of_forall_not_mem

#check Set.eq_empty_of_forall_notMem

/-
Use the lemma `aux` below to show that if `x` is in some `A i`, then there
is a least `i` with that property.
-/
section
open Classical in
-- classical reason for just the following lemma
lemma aux {A : ℕ → Set α} {x : α} (h : ∃ i, x ∈ A i) :
  ∃ i, x ∈ A i ∧ ∀ j < i, x ∉ A j :=
  Subtype.exists_of_subtype (Nat.findX h)

end

theorem aux' {A : ℕ → Set α} {x : α} (h : ∃ i, x ∈ A i) :
  ∃ i, x ∈ A i ∧ ∀ j < i, x ∉ A j :=
  Subtype.exists_of_subtype (Nat.findX h)

include C_def

-- Exercise 4a. [10pts]
theorem disjoint_C_of_lt : ∀ i j, i < j → C i ∩ C j = ∅ := by
  intro i j h
  simp only [C_def]
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_diff,
  Set.mem_iUnion, exists_prop, not_exists,not_and] at hx
  have hxll := hx.left.left
  have hxrr := hx.right.right
  -- now specializing some of these
  have forcontra := hx.right.right i h
  contradiction
-- Exercise 4b. [15pts]
theorem Union_C_eq_Union_A : (⋃ i, C i) = (⋃ i, A i) := by
  apply subset_antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    simp only [C_def] at hx
    rcases hx with ⟨i, hi, hii⟩
    simp only [Set.mem_iUnion]
    use i
  simp only [Set.iUnion_subset_iff]
  intro i x hx
  have : ∃ i, x ∈ A i := by
    use i
  simp only [C_def]
  simp only [Set.mem_iUnion, Set.mem_diff, exists_prop, not_exists, not_and]
  classical
  have aux : ∃ i, x ∈ A i ∧ ∀ j < i, x ∉ A j :=
    Subtype.exists_of_subtype (Nat.findX this)
  rcases aux with ⟨a, ha⟩
  exact ⟨a, ha⟩








end set_sequences
