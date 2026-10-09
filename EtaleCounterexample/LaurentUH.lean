import EtaleCounterexample.AffineUHPowers
import EtaleCounterexample.LaurentUnits
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k]

instance laurent_isDomain : IsDomain (LaurentPolynomial k) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (Polynomial.X : Polynomial k)) _
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero))

instance laurent_isIntegrallyClosed : IsIntegrallyClosed (LaurentPolynomial k) :=
  isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (Polynomial.X : Polynomial k))
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero))

variable (B : Type u) [CommRing B] (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p]

instance laurent_charP : CharP (LaurentPolynomial k) p :=
  (Algebra.charP_iff k (LaurentPolynomial k) p).mp inferInstance

/-- Every unit above a genuine affine UH denominator over the Laurent ring
has a p-power equal to a nonzero Laurent monomial in the base. -/
theorem laurentUH_unit_pow_monomial (φ : LaurentPolynomial k →+* B)
    (hφ : universalHomeomorphisms (Spec.map (CommRingCat.ofHom φ))) (b : B) (hb : IsUnit b) :
    ∃ (d : ℕ) (c : k) (m : ℤ), c ≠ 0 ∧
      b ^ (p ^ d) = φ (LaurentPolynomial.C c * T m) := by
  let := φ.toAlgebra
  have hi : Function.Injective φ := by
    intro x y hxy
    apply affineUH_reduction_injective (LaurentPolynomial k) B hφ
    rw [IsScalarTower.algebraMap_apply (LaurentPolynomial k) B (B ⧸ nilradical B),
      IsScalarTower.algebraMap_apply (LaurentPolynomial k) B (B ⧸ nilradical B)]
    exact congrArg (algebraMap B (B ⧸ nilradical B)) hxy
  have hIntegral : φ.IsIntegral :=
    IsIntegralHom.SpecMap_iff.mp (universalHomeomorphism_integral _ hφ)
  have : IsLocalHom φ := hIntegral.isLocalHom hi
  obtain ⟨d, a, ha⟩ := affineUH_pow_mem (LaurentPolynomial k) B p hφ b
  change φ a = b ^ (p ^ d) at ha
  have hau : IsUnit a := isUnit_of_map_unit φ a (by rw [ha]; exact hb.pow _)
  obtain ⟨c, m, hc, rfl⟩ := (laurent_isUnit_iff a).mp hau
  exact ⟨d, c, m, hc, ha.symm⟩

end EtaleCounterexample
