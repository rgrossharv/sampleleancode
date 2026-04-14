import Mathlib.Tactic
import Mathlib.Data.Nat.Factors
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

set_option warningAsError false
--note a new option set for `  induction'  ` tactic
set_option linter.style.induction false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.flexible false


/- This assignment is due by 11:59pm on Friday, April 10th 2026. -/

/-
EXERCISE 1. Using the definition `mypow a n`, which is supposed to define
exponentiation `a^n`, use induction to prove the theorem below.

Hint: you can use `nat.add_succ` to unfold the defition of `m + n.succ`.
-/

section
variable {α : Type*} [CommMonoid α]


def mypow : α → ℕ → α
| a , 0       => 1
| a , (n + 1) => a * (mypow a n)

#eval mypow 3 5

theorem mypow_zero (a : α) : mypow a 0 = 1 := rfl

theorem mypow_succ (a : α) (n : ℕ) : mypow a (n + 1) = a * mypow a n := rfl

-- Exercise 1 [10pts].
theorem mypow_add (a : α) (m n : ℕ) : mypow a (m + n) = mypow a m * mypow a n := by
  induction' m with m hm
  · rw [Nat.zero_add, mypow_zero, one_mul]
  rw [mypow_succ, mul_assoc, ← hm, ← mypow_succ, Nat.add_right_comm]
end

/-
EXERCISE 2.

In class, we have used ordinary induction on the natural numbers,
which allows you to prove `p n` for an arbitrary natural number
`n` by proving `p 0` and `∀ m, p m → p m.succ`.

It is often more useful to the principle of *complete induction*
or *strong induction*. This is found in the library under the
name `Nat.strong_induction_on`, but the exercise below asks you
to prove it independently, using ordinary induction on the natural numbers.
The principle is stated in a form that the induction tactic
can use it, as illustrated in exercise 3.

The trick is to prove the stronger claim `∀ n, ∀ m < n, p m` by
induction on the natural numbers. The `suffices` step in the proof
shows that this suffices to establish `p n` for the *particular* `n` in
the context. Once we have done that, we throw away the particular `n`,
and focus on proving the stronger claim by induction.
-/

section

-- Exercise 2 [17pts].
theorem complete_induction_on {p : ℕ → Prop} (n : ℕ)
  (h : ∀ n, (∀ m < n, p m) → p n) : p n := by
  suffices : ∀ n, ∀ m < n, p m
  { have := this n
    have yes := h n
    have := yes this
    exact this }
  clear n
  intro n
  induction' n with n ih
  { simp only [not_lt_zero, IsEmpty.forall_iff, implies_true] }
  intro m ha
  have := Nat.lt_add_one_iff_lt_or_eq.mp ha
  rcases this with h1 | h2
  · exact ih m h1
  rw [h2]
  exact h n ih

end

/-
EXERCISE 3.

In this exercise, we use the principle of strong induction to show that
every natural number greater than or equal to two has a prime divisor.

You can use the lemma `exists_lt_dvd_of_not_prime`. After the boilerplate
that we have set up for you, you should formalize the following argument:
if `n` is prime, we are done.  If `n` is not prime, the lemma tells us that
there it has a nontrivial divisor `m < n`, and we can apply the induction
hypothesis to that.
-/

-- This follows straightforwardly from the definition of `nat.prime`.
lemma exists_lt_dvd_of_not_prime {n : Nat} (h : ¬ Nat.Prime n) (h' : 2 ≤ n) :
  ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n := by
  simp [Nat.prime_def_lt'] at h
  exact h h'

example (a b c : ℕ) (h : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  exact Nat.dvd_trans h h2

-- Exercise 3 [18pts].
theorem exists_prime_dvd (n : ℕ) : 2 ≤ n → ∃ p, Nat.Prime p ∧ p ∣ n := by
  induction' n using complete_induction_on with n ih
  intro nle
  by_cases h : Nat.Prime n
  · use n
  have := exists_lt_dvd_of_not_prime h nle
  rcases this with ⟨m, hm1, hm2, hm3⟩
  have := ih m hm2 hm1
  rcases this with ⟨p, hp1, hp2⟩
  use p
  constructor
  · exact hp1
  exact Nat.dvd_trans hp2 hm3

/-
EXERCISE 4.

Finally, in this exercise, we define the structure of a `quasigroup`,
show that the integers with subtraction form an instance, and prove
some basic properties.

You can find the definition of a quasigroup here:

  https://en.wikipedia.org/wiki/Quasigroup

We'll use the notation `ldiv a b` for left division (on Wikipedia, `a \ b`),
and we'll use `rdiv a b` for right division (on Wikipedia, `a / b`).

(Instantiating the integers as a quasigroup is dangerous, because it
redefines the notation of multiplication to mean substraction. Such
a thing could destroy the understanding of mathematics for a generation
of elementary school students, so please make sure your git repositories
stay private!)
-/

-- Exercise 4a [10pts].
/-
First, fill in the remaining axioms. E.g. the first should say,
"for any `a`, `b` and `x`, if `x` satisfies the defining equation for `a \ b`
(that is, the cancellation law), then it is equal to `a \ b`."
-/

class quasigroup (α : Type*) extends Mul α where
(ldiv : α → α → α)
(rdiv : α → α → α)
(mul_ldiv_cancel : ∀ a b, a * ldiv a b = b)
(rdiv_mul_cancel : ∀ a b, rdiv a b * b = a)
(ldiv_unique : ∀ a b x, a * x = b → x = ldiv a b)
(rdiv_unique : ∀ a b x, x * b = a → x = rdiv a b)

/-
class quasigroup (α : Type*) extends Mul α :=
(ldiv : α → α → α)
(rdiv : α → α → α)
(mul_ldiv_cancel : ∀ a b, a * ldiv a b = b)
(rdiv_mul_cancel : ∀ a b, rdiv a b * b = a)
(ldiv_unique : sorry)
(rdiv_unique : sorry)
-/
-- Exercise 4b [15pts].
/-
Next, show that the integers with subtraction are an instance. You will
have to figure out the right definitions of `ldiv` and `rdiv`. For
example, if you decide `ldiv a b` should be `a * b`, write
`ldiv := λ a b, a * b`.

Note: Be sure to write this out on paper first, and check the identities
as you see them wikipedia.  This will make the coding much easier, and
help avoid you trying to prove something that is impossible.

Note that in goals within the instance definition, you might see "multiplication"
which is really integer subtraction, because that's we defined it as! To check
which one it really is, you can click on the `*` operation in the infoview and look
for something like `{mul := int.sub}`.

Also, the `show` tactic can sometimes be used to unfold definitions. For example
on the goal `⊢ a * b = stuff`, `show a - b = stuff` should work.
-/
--it got mad at me for using show and lambda you should look into this for future lean 4 classes
instance : quasigroup ℤ where
  mul  := Int.sub
  ldiv := fun a b => a - b
  rdiv := fun a b => a + b
  mul_ldiv_cancel := by
    intro a b
    change a - (a - b) = b
    linarith
  rdiv_mul_cancel := by
      intro a b
      change (a+b)-b = a
      linarith
  ldiv_unique := by
      intro a b x h
      change a - x = b at h
      linarith
  rdiv_unique := by
      intro a b x h
      change x - b = a at h
      linarith

/- Finally, prove that some identities hold in *any* quasigroup. -/

namespace quasigroup
variable {α : Type*} [quasigroup α]

-- Exercise 4c [5pts].
theorem eq_ldiv_mul_self (y x : α) : y = ldiv x (x * y) := by
  rw [← ldiv_unique]
  rfl

-- Exercise 4d [5pts].
theorem eq_mul_rdiv_self (y x : α) : y = rdiv (y * x) x := by
  rw [← rdiv_unique]
  rfl

-- Exercise 4e [10pts].
theorem left_cancel (a b c : α) (h : a * b = a * c) : b = c := by
  have really1 : a * b = a * b := by rfl
  have h1 := ldiv_unique a (a * b) b really1
  have h2 := ldiv_unique a (a * b) c ?_
  · rw [h1, h2]
  rw [← h]

-- Exercise 4f [10pts].
theorem right_cancel (a b c : α) (h : a * b = c * b) : a = c := by
  have h1 := rdiv_unique (a*b) b a ?_
  have h2 := rdiv_unique (a*b) b c ?_
  · rw[h1,h2]
  · rw[h]
  rfl

end quasigroup
