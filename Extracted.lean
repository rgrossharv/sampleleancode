-- LeanTeX generated file. Do not edit manually.

import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

-- BEGIN_SNIPPET 1
-- LeanTeX hoisted import: import Mathlib.RingTheory.Ideal.Maximal
-- LeanTeX hoisted import: import Mathlib.RingTheory.Ideal.Defs
-- LeanTeX hoisted import: import Mathlib.RingTheory.Polynomial.Quotient
-- LeanTeX hoisted import: import Mathlib.RingTheory.Polynomial.Basic
-- LeanTeX hoisted import: import Mathlib.Data.ZMod.QuotientRing
-- LeanTeX hoisted import: import Mathlib.Algebra.Field.IsField
-- LeanTeX hoisted import: import Mathlib.Data.ZMod.Defs
-- LeanTeX hoisted import: import Mathlib.Algebra.Field.IsField
-- LeanTeX hoisted import: import Mathlib.Algebra.Field.Basic
-- LeanTeX hoisted import: import Mathlib.Tactic
-- END_SNIPPET 1

-- BEGIN_SNIPPET 2
open Polynomial

noncomputable def I : Ideal ℤ[X] := Ideal.span {2,X}
noncomputable def J : Ideal ℤ[X] := Ideal.span {4,X}
-- END_SNIPPET 2

-- BEGIN_SNIPPET 3
theorem Iismaximal : I.IsMaximal := by 
  apply Ideal.Quotient.maximal_of_isField I
  have ZxquotIZmod2 : (ℤ[X] ⧸ I) ≃* (ℤ ⧸ (Ideal.span {2} : Ideal ℤ)) := by 
    have := Polynomial.quotientSpanCXSubCAlgEquiv (R := ℤ) 2 0
    have idealrfl : Ideal.span {C 2, X - C 0} = I := by 
      simp only [eq_intCast, Int.cast_ofNat, Int.cast_zero, sub_zero]
      rfl
    rw [idealrfl] at this
    have := this.toMulEquiv 
    exact this
  have zquotideal2eqzmod2 : ℤ ⧸ (Ideal.span {2} : Ideal ℤ) ≃* ZMod 2 := by 
    apply (Int.quotientSpanEquivZMod 2).toMulEquiv 
  have : (ℤ[X] ⧸ I) ≃* ZMod 2 := by 
    exact ZxquotIZmod2.trans zquotideal2eqzmod2
  have zmod2isfield : IsField (ZMod 2) := by 
    exact Semifield.toIsField (ZMod 2)
  exact MulEquiv.isField zmod2isfield this
-- END_SNIPPET 3

-- BEGIN_SNIPPET 4
theorem Jisprimary : J.IsPrimary := by 
  have jradeqi : I = J.radical := by 
    rw[Ideal.ext_iff]
    intro x
    constructor
    · intro h 
      rw [Ideal.mem_radical_iff]
      have := Ideal.mem_span_pair.mp h 
      rcases this with ⟨a, b, hab⟩
      rw [← hab]
      use 2
      apply Ideal.mem_span_pair.mpr 
      use (a*b*X +a^2)
      use (b^2 * X)
      ring_nf 
    intro h 
    rw [Ideal.mem_radical_iff] at h 
    rcases h with ⟨r,hr⟩ 
    have jsubseti : J ≤ I := by 
      apply Ideal.span_le.mpr 
      simp [Set.subset_def]
      constructor
      · apply Ideal.mem_span_pair.mpr
        use 2
        use 0
        ring
      apply Ideal.mem_span_pair.mpr
      use (-X)
      use 3
      ring
    have Iprime : I.IsPrime := by 
      exact Ideal.IsMaximal.isPrime Iismaximal
    have : x ^ r ∈ I := by 
      exact jsubseti hr 
    exact Ideal.IsPrime.mem_of_pow_mem Iprime r (jsubseti hr)
  have : J.radical.IsMaximal := by 
    rw [← jradeqi]
    exact Iismaximal
  exact Ideal.isPrimary_of_isMaximal_radical this
-- END_SNIPPET 4
