import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs

lemma yes (a b : ℕ) (ha : 1 < a) (h : a ≤ b) : ¬ (a ∣ b.factorial + 1) := by
  by_contra!
  have hfac : a ∣ b.factorial := by
    apply Nat.dvd_factorial _ h
    linarith
  have hone : a ∣ (b.factorial + 1) - b.factorial := by
    exact Nat.dvd_sub this hfac
  have h2 : a ∣ 1 := by
    exact (Nat.dvd_add_iff_right hfac).mpr this
  have : a = 1 := Nat.dvd_one.mp h2
  have : ¬ 1 < a := by
    linarith
  contradiction

theorem infmanyprimes : ∀ (n : ℕ), ∃ p : ℕ, Nat.Prime p ∧ p > n := by
  by_contra!
  rcases this with ⟨n, hn⟩
  set m := (Nat.factorial n) +1 with hm
  have h2 : m ≠ 1 := by
    rw [hm]
    by_contra!
    have yes (a : ℕ) (h : a + 1 = 1) : a = 0:= by
      linarith
    have final := yes n.factorial this
    have := Nat.factorial_ne_zero n
    contradiction
  have primedivm : ∃ p : ℕ, Nat.Prime p ∧ p ∣ m := by
    exact Nat.exists_prime_and_dvd h2
  rcases primedivm with ⟨k, hk⟩
  have : k > n := by
    by_contra!
    have kgt1 : 1 < k := by
      have kprime := hk.left
      exact Nat.Prime.one_lt kprime
    have and2 := yes k n kgt1 this
    have forcontra1 := hk.right
    rw [hm] at forcontra1
    contradiction
  have hkl := hk.left
  have hkr := hk.right
  specialize hn k hk.left
  have forcontra : ¬ k ≤ n := by
    exact Nat.not_le_of_lt this
  contradiction