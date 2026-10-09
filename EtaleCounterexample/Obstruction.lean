import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option autoImplicit false

/-!
The algebraic point-action obstruction, with all hypotheses explicit.
There is no assertion here that a particular relative étale equivalence has
this action, nor that every localized scheme morphism is monomial.
-/

namespace EtaleCounterexample
open Polynomial
universe u
variable {K : Type u} [Field K]

/-- Over any field, integer powers agreeing on an infinite set of nonzero
elements have equal exponents. Negative exponents are included. -/
theorem exponents_eq_of_infinite
    {S : Set K} (hS : S.Infinite) (h0 : ∀ z ∈ S, z ≠ 0)
    {m n : ℤ} (h : ∀ z ∈ S, z ^ m = z ^ n) : m = n := by
  have hz : ∀ z ∈ S, z ^ (m - n) = 1 := by
    intro z hz
    rw [zpow_sub₀ (h0 z hz), h z hz, div_self (zpow_ne_zero _ (h0 z hz))]
  have hn : ∀ z ∈ S, z ^ (m - n).natAbs = 1 := by
    intro z hs
    rw [← zpow_natCast, Int.natCast_natAbs]
    rcases le_total 0 (m - n) with hpos | hneg
    · rw [abs_of_nonneg hpos, hz z hs]
    · rw [abs_of_nonpos hneg, zpow_neg, hz z hs, inv_one]
  have hp : (X : K[X]) ^ (m - n).natAbs = 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hS.mono
    intro z hs
    simpa using hn z hs
  have hdeg := congrArg Polynomial.natDegree hp
  simp only [natDegree_X_pow, natDegree_one] at hdeg
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hdeg)

/-- Clearing the `p^d` denominator is enough for nonalgebraicity of a point
action: an automorphism fixing infinitely many nonzero elements cannot have a
monomial action of this form unless it is the identity. This is conditional on
the fixed-set and monomial hypotheses, not a counterexample theorem. -/
theorem automorphism_eq_one_of_monomial
    (σ : K ≃+* K) {S : Set K} (hS : S.Infinite)
    (h0 : ∀ z ∈ S, z ≠ 0) (hfix : ∀ z ∈ S, σ z = z)
    (r : ℕ) (hr : Function.Injective (fun z : K ↦ z ^ r))
    (m : ℤ) (c : K)
    (hmono : ∀ z : K, z ≠ 0 → (σ z) ^ r = c * z ^ m) : σ = 1 := by
  have hc : c = 1 := by simpa using (hmono 1 one_ne_zero).symm
  have hm : m = (r : ℤ) := exponents_eq_of_infinite hS h0 (by
    intro z hz
    have := hmono z (h0 z hz)
    simpa [hc, hfix z hz] using this.symm)
  ext z
  by_cases hz : z = 0
  · simp [hz]
  · apply hr
    simpa [hc, hm] using hmono z hz

/-- A moved point contradicts the cleared monomial formula under the same
explicit fixed-set and power-injectivity assumptions. -/
theorem no_monomial_of_infinite_fixed
    (σ : K ≃+* K) {S : Set K} (hS : S.Infinite)
    (h0 : ∀ z ∈ S, z ≠ 0) (hfix : ∀ z ∈ S, σ z = z)
    (hne : ∃ z, σ z ≠ z)
    (r : ℕ) (hr : Function.Injective (fun z : K ↦ z ^ r)) :
    ¬ ∃ (c : K) (m : ℤ), ∀ z : K, z ≠ 0 → (σ z) ^ r = c * z ^ m := by
  rintro ⟨c, m, h⟩
  have he := automorphism_eq_one_of_monomial σ hS h0 hfix r hr m c h
  obtain ⟨z, hz⟩ := hne
  exact hz (by rw [he]; rfl)

end EtaleCounterexample
