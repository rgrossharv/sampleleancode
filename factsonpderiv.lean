import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Defs

section
--These are defined so we work on partial derivatives with ℝ (one dimensional) output
variable {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (i j : Fin n) (x : Fin n → ℝ) (f' g' : (Fin n → ℝ) →L[ℝ] ℝ)

noncomputable def pderivonedim (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
(fderiv ℝ f x) (Pi.single i 1)

--Partial (one dimensional) of a constant function is 0
example (c : ℝ) : pderivonedim (fun _ => c) i x = 0 := by
  unfold pderivonedim
  rw [fderiv_fun_const]
  rfl

--Partial of (f+g) is the partial of f + partial of g
example (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
pderivonedim (f + g) i x = pderivonedim f i x + pderivonedim g i x := by
  unfold pderivonedim
  rw [fderiv_add]
  · rfl
  · exact HasFDerivAt.differentiableAt hf
  exact HasFDerivAt.differentiableAt hg

--Product Rule
example (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
pderivonedim (f * g) i x = (pderivonedim f i x) * g x + (pderivonedim g i x) * f x := by
  unfold pderivonedim
  rw [fderiv_mul]
  · simp [add_comm, mul_comm]
  · exact HasFDerivAt.differentiableAt hf
  exact HasFDerivAt.differentiableAt hg

--Interior Extremum Theorem
example (localextrema : IsLocalExtr f a) : pderivonedim f i a = 0 := by
  unfold pderivonedim
  rw [IsLocalExtr.fderiv_eq_zero]
  swap
  · exact localextrema
  rfl

--Elementary Clairaut's Theorem (See Bryan Wang)
example (hf : ContDiff ℝ 2 f) : pderivonedim (pderivonedim f i) j x = pderivonedim (pderivonedim f j) i x := by
  unfold pderivonedim
  sorry

--May want to eventually prove Taylor's Theorem

end
