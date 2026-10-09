import EtaleCounterexample.UniversalHomeomorphisms
import EtaleCounterexample.RadicialPowers

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u
variable (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [Algebra A B]

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- A UH map of affine schemes is injective on ring homomorphisms to fields,
with the base map held fixed. This is the actual scheme-to-algebra bridge. -/
theorem affineUH_fieldHom_injective
    (h : universalHomeomorphisms (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (K : Type u) [Field K] : Function.Injective
      (fun g : B →+* K ↦ g.comp (algebraMap A B)) := by
  intro g g' he
  have H : Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom g') :=
    universalHomeomorphism_fieldPoints_injective _ h K (by
      dsimp only
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun a : A →+* K ↦ Spec.map (CommRingCat.ofHom a)) he)
  exact CommRingCat.hom_ext_iff.mp (Spec.map_injective H)

omit [IsIntegrallyClosed A] in
/-- Surjectivity of the affine spectrum map embeds a reduced base into the
reduction of the source. -/
theorem affineUH_reduction_injective
    (h : universalHomeomorphisms (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    Function.Injective (algebraMap A (B ⧸ nilradical B)) := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) :=
    (universalHomeomorphism_homeomorph _ h).surjective
  have hq := PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    (R := B) (I := nilradical B) le_rfl
  have hcomp : Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (B ⧸ nilradical B))) := hsurj.comp hq.surjective
  have hk := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap A (B ⧸ nilradical B))).mp hcomp.denseRange
  rw [RingHom.injective_iff_ker_eq_bot]
  exact le_antisymm (hk.trans (nilradical_eq_bot_iff.mpr inferInstance).le) bot_le

variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- An actual affine UH over a normal domain has the p-power descent property,
without a reducedness assumption on its source. -/
theorem affineUH_pow_mem
    (h : universalHomeomorphisms (Spec.map (CommRingCat.ofHom (algebraMap A B)))) (b : B) :
    ∃ n : ℕ, b ^ (p ^ n) ∈ (algebraMap A B).range := by
  have hi : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    universalHomeomorphism_integral _ h
  have : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp
    (IsIntegralHom.SpecMap_iff.mp hi)
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap (algebraMap A B)) :=
    universalHomeomorphism_homeomorph _ h
  have : IrreducibleSpace (PrimeSpectrum B) :=
    hhomeo.homeomorph.irreducibleSpace_iff.mpr inferInstance
  have : (nilradical B).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  exact radicial_integral_normal_pow_mem_nonreduced A B p
    (affineUH_reduction_injective A B h) (affineUH_fieldHom_injective A B h) b

end EtaleCounterexample
