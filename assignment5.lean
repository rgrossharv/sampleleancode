import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option warningAsError false

/-
# Homework assignment 5

- Homework 5 is due on Friday, March 6
  It is worth 70 points, and the goal is to
  formalize a complete proof of the
  Intermediate Value Theorem.
-/

/-
# The intermediate value theorem
-/

def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

def continuous (f : ℝ → ℝ) := ∀ a, approaches_at f (f a) a


section
variable (a b : ℝ) (f : ℝ → ℝ) (S : Set ℝ)

#check sSup S

#check @sSup
#check sSup { x : ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0 }

#check le_csSup
#check @le_csSup

#check csSup_le
#check @csSup_le

#print BddAbove
#print upperBounds

#check exists_lt_of_lt_csSup
#check @exists_lt_of_lt_csSup

#check Mathlib.Tactic.linarith

-- I finished the theorem in the second theorem below
--since I did it in the assignment file first!

theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 := by
  let S := { x: ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have ainS : a ∈ S := by
    -- or constructor twice
    exact ⟨le_refl a ,aleb , hfa⟩
  have bddS : BddAbove S := by
    use b
    intro s sinS
    --exact sinS.2.1
    exact sinS.right.left
  --set c := sSup S with cdef -- gives a _name_ to fact c= sSup S
  let c := sSup S
  --Next: establish c ∈ [a,b]
  have cdef : c = sSup S := by --instead of using `set`
    rfl

  have cleb : c ≤ b := by
    apply csSup_le
      --in term mode:
      --exact ⟨a, ainS⟩
    · use a
    intro s sinS
    exact sinS.2.1
  have alec : a ≤ c := by
    exact le_csSup bddS ainS
  --**Big step---cases on f(c) vs 0
  rcases lt_trichotomy (f c) 0 with fcneg | fczero | fcpos
    --Case 1
  · exfalso
    unfold continuous at ctsf
    specialize ctsf c
    set ε := - (f c)/2 with εdef
    have εpos : ε > 0 := by
      linarith
    unfold approaches_at at ctsf
    specialize ctsf ε εpos
    rcases ctsf with ⟨ δ, δpos, hδ⟩
    by_cases hc2: c + δ/2 > b
    · have bnearc : |b-c| < δ := by
        rw [abs_lt]
        constructor <;> linarith
      specialize hδ b bnearc
      have forcontra : ¬ 0 < f b
      { rw [abs_lt] at hδ
        linarith
      }
      apply forcontra
      exact hfb
    -- Now in case where c + δ/2 ≤ b
    push_neg at hc2
    have c2nearc : |c + δ/2 -c| < δ := by
      rw [add_sub_cancel_left]
      rw [abs_of_pos] <;> linarith
    specialize hδ (c + δ/2) c2nearc
    -- here is where class ended on 3/2 --
    /- PROBLEM 1: [10pts] Finish the proof by replacing
                  the `sorry` statements -/
    have hfc2neg : f (c + δ/2) < 0 := by
      sorry
    have c2inS : c + δ/2 ∈ S := by
      sorry
    have c2lec : c + δ/2 ≤ c := by
      sorry
    sorry
    --At this pont, Case 1 where f c < 0 is finished
  · --now on to Case 2
    /-PROBLEM 2: [3pts] Complete the proof of this
      case, where f c = 0 -/
    sorry
  · --finally Case 3, where 0 < f c
    /- PROBLEM 3: [57pts] Complete the proof of
       the third case below.  You can follow the
       outline in the pdf lecture0302-ivt.pdf
       in the course directory.  Note that the pdf
       is written to reasonably precisely line up
       with a possible Lean code formalization.-/
    sorry


theorem ivt2 {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 := by
  unfold continuous at ctsf
  let S := {x : ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have ainS: a ∈ S := by
    exact ⟨le_refl a, aleb , hfa⟩
  have bddS : BddAbove S := by
    use b
    intro s sinS
    exact sinS.right.left
  set c := sSup S with cdef
  have cleb : c ≤ b := by
    apply csSup_le
    · use a
    intro h hinS
    exact hinS.right.left
  have alec : a ≤ c := by
    exact le_csSup bddS ainS
  rcases lt_trichotomy (f c) 0 with fcneg | fc0 | fcpos
  swap
  · use c
  · exfalso
    specialize ctsf c
    set ε := -(f c)/2 with he
    have expos : ε > 0 := by
      linarith
    unfold approaches_at at ctsf
    specialize ctsf ε expos
    rcases ctsf with ⟨δ, δpos, hδ⟩
    by_cases hc2 : c + δ/2 > b
    · have bnearc : |b - c| < δ := by
        rw [abs_lt]
        constructor <;> linarith
      specialize hδ b bnearc
      have forcontra : ¬ 0 < f b := by
        rw [abs_lt] at hδ
        linarith
      contradiction
    -- Now in the case where c + δ/2 is less than or equal to b
    push_neg at hc2
    have c2nearc : |c + δ/2 - c| < δ := by
      rw [add_sub_cancel_left]
      have deltatwopos : δ/2 > 0 := by
        exact half_pos δpos
      rw [gt_iff_lt] at deltatwopos
      rw [abs_of_pos]
      · linarith
      exact deltatwopos
    specialize hδ (c + δ/2) c2nearc
    -- here is where class ended on 3/2 --
    /- PROBLEM 1: [10pts] Finish the proof by replacing
                  the `sorry` statements -/
    have hfc2neg : f (c + δ/2) < 0 := by
      rw [he] at hδ
      rw[abs_lt] at hδ
      have := hδ.left
      have := hδ.right
      linarith
    have c2inS : c + δ/2 ∈ S := by
      have deltatwopos : δ/2 > 0 := by
        exact half_pos δpos
      have part1 : a ≤ c + δ/2 := by
        linarith
      exact ⟨part1, hc2, hfc2neg⟩
    have c2lec : c + δ/2 ≤ c := by
      exact le_csSup bddS c2inS
    have forcontra2 : ¬ (c + δ/2 ≤ c) := by
      linarith
    contradiction
    --At this pont, Case 1 where f c < 0 is finished
    --now on to Case 2 (done under different structure)
  --finally Case 3, where 0 < f c
    /- PROBLEM 3: [57pts] Complete the proof of
       the third case below.  You can follow the
       outline in the pdf lecture0302-ivt.pdf
       in the course directory.  Note that the pdf
       is written to reasonably precisely line up
       with a possible Lean code formalization.-/
  exfalso
  specialize ctsf c
  set ε := (f c)/2 with he
  have εpos : ε > 0 := by
    exact half_pos fcpos
  unfold approaches_at at ctsf
  specialize ctsf ε εpos
  rcases ctsf with ⟨δ, δpos, hδ⟩
  have clearly : c - δ/2 < c := by
    linarith
  have cmindtwolts : ∃ s ∈ S, c - δ/2 < s := by
    apply exists_lt_of_lt_csSup
    swap
    · exact clearly
    use a
  rcases cmindtwolts with ⟨s, hs⟩
  have hsleft := hs.left
  have hsright := hs.right
  have cminsltd : abs (c - s) < δ := by
    rw[abs_lt]
    constructor
    swap
    · linarith
    have : s ≤ c := by
      apply le_csSup bddS hsleft
    linarith
  have smincltd : abs (s-c) < δ := by
    rw[abs_sub_comm]
    exact cminsltd
  specialize hδ s smincltd
  rw [he] at hδ
  rw [abs_lt] at hδ
  have hleft := hδ.left
  have hright := hδ.right
  have fspos : 0 < f s := by
    linarith
  have fsneg : f s < 0 := by
    exact hsleft.right.right
  have forcontra3 : ¬ (0 < f s ) := by
    linarith
  contradiction

end
