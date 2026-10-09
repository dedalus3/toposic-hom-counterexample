import EtaleCounterexample.LocalizedMonomial
import EtaleCounterexample.NonintegralTwist
import EtaleCounterexample.ProfiniteExponent

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP Ω p]

include p in
/-- No actual localized algebraic endomorphism has the explicit nonintegral
point action. This is an unconditional statement about the scheme localization.
The implication from a relative topos isomorphism to equality of these actions
is a separate, still required comparison theorem. -/
theorem nonintegral_action_not_localized_scheme_action
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    ¬ ∀ z : Ωˣ,
      multiplicativeGroupCoordinate k Ω
        ((localizedSchemePoints (fieldGeometricPoint k Ω)).map a
          (multiplicativeGroupRelativePoint k Ω z)) =
        nonintegralFieldAutomorphism k Ω (z : Ω) := by
  intro he
  obtain ⟨d, c, m, _, h⟩ := localizedEndomorphism_monomial_pointAction k Ω p a
  apply nonintegralFieldAutomorphism_no_monomial k Ω p d
  refine ⟨algebraMap k Ω c, m, ?_⟩
  intro z hz
  have H := h (Units.mk0 z hz)
  rw [he] at H
  exact H

omit [IsAlgClosed Ω] in
/-- The finite-period action characterizes the constructed automorphism
uniquely; this ties the CRT inverse-limit exponent to a single global action. -/
theorem nonintegralFieldAutomorphism_unique
    (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ (n : ℕ), n ≠ 0 → ∀ z : Ω,
      z ^ (Fintype.card k ^ n) = z → σ z = z ^ (Fintype.card k ^ twoPrimaryResidue n)) :
    σ = nonintegralFieldAutomorphism k Ω := by
  ext z
  obtain ⟨n, hn, hz⟩ := finiteFieldFrobenius_locallyPeriodic k Ω z
  have hz' : z ^ (Fintype.card k ^ n) = z := by
    simpa only [Function.IsPeriodicPt, Function.IsFixedPt,
      FiniteField.coe_frobeniusAlgHom, pow_iterate] using hz
  exact (hσ n hn z hz').trans (nonintegralFieldAutomorphism_period k Ω hn z hz').symm

end EtaleCounterexample
