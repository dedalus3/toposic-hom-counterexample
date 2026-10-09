import EtaleCounterexample.PeriodicPower
import EtaleCounterexample.FiniteFields
import EtaleCounterexample.FiniteFieldBaseTwist

set_option autoImplicit false
noncomputable section
open Function
namespace EtaleCounterexample
universe u v
variable (k : Type u) [Field k] [Fintype k]
  (Ω : Type v) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

theorem finiteFieldFrobenius_locallyPeriodic (x : Ω) :
    ∃ n : ℕ, n ≠ 0 ∧ IsPeriodicPt (FiniteField.frobeniusAlgHom k Ω) n x := by
  let E := IntermediateField.adjoin k {x}
  have : FiniteDimensional k E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite E := Module.finite_of_finite k
  let y : E := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩
  obtain ⟨n, hn, hy⟩ :=
    (FiniteField.frobeniusAlgEquivOfAlgebraic k E).injective.mem_periodicPts y
  refine ⟨n, hn.ne', ?_⟩
  have h : Semiconj (fun z : E ↦ (z : Ω))
      (FiniteField.frobeniusAlgEquivOfAlgebraic k E) (FiniteField.frobeniusAlgHom k Ω) := by
    intro z
    exact map_pow E.subtype z (Fintype.card k)
  exact hy.map h

/-- The actual automorphism whose Frobenius exponents are one on the 2-primary
part and zero on the odd part of every finite period. -/
def nonintegralFieldAutomorphism : Ω ≃ₐ[k] Ω :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom k Ω).symm
    (twoPrimaryAlgHom (FiniteField.frobeniusAlgHom k Ω)
      (finiteFieldFrobenius_locallyPeriodic k Ω))

@[simp] theorem nonintegralFieldAutomorphism_apply (z : Ω) :
    nonintegralFieldAutomorphism k Ω z =
      twoPrimaryIterate (FiniteField.frobeniusAlgHom k Ω) z := rfl

/-- Exact finite-period connection to the compatible residue system. -/
theorem nonintegralFieldAutomorphism_period {n : ℕ} (hn : n ≠ 0) (z : Ω)
    (hz : z ^ (Fintype.card k ^ n) = z) :
    nonintegralFieldAutomorphism k Ω z =
      z ^ (Fintype.card k ^ twoPrimaryResidue n) := by
  have h : IsPeriodicPt (FiniteField.frobeniusAlgHom k Ω) n z := by
    simpa only [IsPeriodicPt, IsFixedPt, FiniteField.coe_frobeniusAlgHom, pow_iterate] using hz
  rw [nonintegralFieldAutomorphism_apply, twoPrimaryIterate_eq hn h]
  exact congrFun (pow_iterate (Fintype.card k) _) z

/-- This single global automorphism fixes the entire odd-degree locus. -/
theorem nonintegralFieldAutomorphism_odd_fixed (z : Ω) (hz : z ∈ oddDegreeElements k Ω) :
    nonintegralFieldAutomorphism k Ω z = z := by
  obtain ⟨n, hn, hz⟩ := hz
  apply twoPrimaryIterate_odd hn
  simpa only [IsPeriodicPt, IsFixedPt, FiniteField.coe_frobeniusAlgHom, pow_iterate,
    Fintype.card_eq_nat_card] using hz

/-- On the quadratic fixed field, this automorphism is arithmetic Frobenius. -/
theorem nonintegralFieldAutomorphism_quadratic (z : Ω)
    (hz : z ^ (Nat.card k ^ 2) = z) :
    nonintegralFieldAutomorphism k Ω z = z ^ Nat.card k := by
  have h : IsPeriodicPt (FiniteField.frobeniusAlgHom k Ω) 2 z := by
    simpa only [IsPeriodicPt, IsFixedPt, FiniteField.coe_frobeniusAlgHom, pow_iterate,
      Fintype.card_eq_nat_card] using hz
  rw [nonintegralFieldAutomorphism_apply]
  simpa only [FiniteField.coe_frobeniusAlgHom, Fintype.card_eq_nat_card] using
    twoPrimaryIterate_two h

/-- The selected global action is central in the actual group of k-automorphisms. -/
theorem nonintegralFieldAutomorphism_central (τ : Ω ≃ₐ[k] Ω) :
    nonintegralFieldAutomorphism k Ω * τ = τ * nonintegralFieldAutomorphism k Ω := by
  ext z
  obtain ⟨n, hn, hz⟩ := finiteFieldFrobenius_locallyPeriodic k Ω z
  exact (twoPrimaryIterate_natural τ (fun x ↦ map_pow τ x (Fintype.card k)) hn hz).symm

variable (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed Ω]

include p in
/-- The global automorphism is nontrivial, including in characteristic two. -/
theorem nonintegralFieldAutomorphism_moves :
    ∃ z : Ω, nonintegralFieldAutomorphism k Ω z ≠ z := by
  obtain ⟨z, _, hz⟩ := quadratic_frobenius_moves k p
  let a : FiniteField.Extension k p 2 →ₐ[k] Ω := IsAlgClosed.lift
  refine ⟨a z, ?_⟩
  have hz2 : (a z) ^ (Nat.card k ^ 2) = a z := by
    rw [← map_pow]
    congr 1
    let := Fintype.ofFinite (FiniteField.Extension k p 2)
    rw [← FiniteField.natCard_extension k p 2, ← Fintype.card_eq_nat_card]
    exact FiniteField.pow_card z
  rw [nonintegralFieldAutomorphism_quadratic k Ω _ hz2, ← map_pow]
  exact fun h ↦ hz (a.injective h)

/-- An unconditional field-level obstruction for the explicitly constructed
single global automorphism. The scheme-localization bridge is separate. -/
theorem nonintegralFieldAutomorphism_no_monomial [CharP Ω p] (d : ℕ) :
    ¬ ∃ (c : Ω) (m : ℤ), ∀ z : Ω, z ≠ 0 →
      (nonintegralFieldAutomorphism k Ω z) ^ (p ^ d) = c * z ^ m :=
  no_monomial_of_odd_fixed k p Ω (nonintegralFieldAutomorphism k Ω).toRingEquiv
    (nonintegralFieldAutomorphism_odd_fixed k Ω)
    (nonintegralFieldAutomorphism_moves k Ω p) d

end EtaleCounterexample
