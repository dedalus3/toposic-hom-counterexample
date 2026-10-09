import EtaleCounterexample.SchemeRoofs
import EtaleCounterexample.LocalizedSchemePoints
import EtaleCounterexample.LaurentUH
import EtaleCounterexample.MultiplicativeGroupPoints

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

def multiplicativeGroupRelativePoint (z : Ωˣ) :
    schemePoints (fieldGeometricPoint k Ω) (multiplicativeGroupFiniteType k) :=
  ⟨multiplicativeGroupPoint k Ω z, multiplicativeGroupPoint_over k Ω z⟩

/-- The Laurent coordinate of an actual relative scheme point. -/
def multiplicativeGroupCoordinate
    (x : schemePoints (fieldGeometricPoint k Ω) (multiplicativeGroupFiniteType k)) : Ω :=
  (Spec.preimage x.val).hom (T (1 : ℤ))

@[simp] theorem multiplicativeGroupCoordinate_point (z : Ωˣ) :
    multiplicativeGroupCoordinate k Ω (multiplicativeGroupRelativePoint k Ω z) = z := by
  change (Spec.preimage (Spec.map (CommRingCat.ofHom
    (laurentEvaluation k Ω z).toRingHom))).hom (T (1 : ℤ)) = _
  rw [Spec.preimage_map]
  change LaurentPolynomial.eval₂ (algebraMap k Ω) z (T (1 : ℤ)) = _
  simp

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The ring formula on any actual finite-type affine UH roof of G_m. -/
theorem multiplicativeGroup_roof_monomial
    (Z : FiniteTypeSchemes (Spec (.of k))) [IsAffine Z.left]
    (s f : Z ⟶ multiplicativeGroupFiniteType k) (hs : relativeUH _ s) :
    ∃ (d : ℕ) (c : k) (m : ℤ), c ≠ 0 ∧
      ∀ (l : Spec (.of Ω) ⟶ Z.left) (z : Ωˣ),
        l ≫ s.left = multiplicativeGroupPoint k Ω z →
        ((Spec.preimage (l ≫ f.left)).hom (T (1 : ℤ))) ^ (p ^ d) =
          algebraMap k Ω c * (z : Ω) ^ m := by
  let B := Γ(Z.left, ⊤)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.left.isoSpec.inv ≫ s.left)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (Z.left.isoSpec.inv ≫ f.left)
  have hUH : universalHomeomorphisms (Spec.map φ) := by
    rw [hφ]
    exact (universalHomeomorphisms.cancel_left_of_respectsIso _ _).mpr hs
  have hsurj : Function.Surjective (PrimeSpectrum.comap φ.hom) :=
    (universalHomeomorphism_homeomorph _ hUH).surjective
  have : Nonempty (PrimeSpectrum B) := ⟨hsurj ⟨⊥, inferInstance⟩ |>.choose⟩
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Algebra k B := (φ.hom.comp (algebraMap k (LaurentPolynomial k))).toAlgebra
  have : CharP B p := (Algebra.charP_iff k B p).mp inferInstance
  obtain ⟨d, c, m, hc, hpow⟩ := laurentUH_unit_pow_monomial k B p φ.hom hUH
    (β.hom (T (1 : ℤ))) ((isUnit_T (1 : ℤ)).map β.hom)
  refine ⟨d, c, m, hc, ?_⟩
  intro l z hl
  let ψ := Spec.preimage (l ≫ Z.left.isoSpec.hom)
  have hls : l ≫ s.left = Spec.map ψ ≫ Spec.map φ := by
    rw [Spec.map_preimage, hφ]
    simp
  have hlf : l ≫ f.left = Spec.map ψ ≫ Spec.map β := by
    rw [Spec.map_preimage, hβ]
    simp
  have hz : φ ≫ ψ = CommRingCat.ofHom (laurentEvaluation k Ω z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hls, hl]
    rfl
  have H := congrArg ψ.hom hpow
  rw [map_pow] at H
  rw [hlf, ← Spec.map_comp, Spec.preimage_map]
  change (ψ.hom (β.hom (T (1 : ℤ)))) ^ (p ^ d) = _
  rw [H]
  change (φ ≫ ψ).hom (C c * T m) = _
  rw [hz]
  change LaurentPolynomial.eval₂ (algebraMap k Ω) z (C c * T m) = _
  simp

variable [IsAlgClosed Ω]

/-- ALL endomorphisms in the actual finite-type UH localization have monomial
point action, in the equivalent p-power form that avoids choosing roots. -/
theorem localizedEndomorphism_monomial_pointAction
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    ∃ (d : ℕ) (c : k) (m : ℤ), c ≠ 0 ∧ ∀ z : Ωˣ,
      (multiplicativeGroupCoordinate k Ω
        ((localizedSchemePoints (fieldGeometricPoint k Ω)).map a
          (multiplicativeGroupRelativePoint k Ω z))) ^ (p ^ d) =
        algebraMap k Ω c * (z : Ω) ^ m := by
  let X := multiplicativeGroupFiniteType k
  let F := localizedSchemePoints (fieldGeometricPoint k Ω)
  have : IsAffine X.left := by
    change IsAffine (Spec (.of (LaurentPolynomial k)))
    infer_instance
  obtain ⟨Z, s, f, hZ, hs, ha⟩ := localizedScheme_morphism_has_affine_roof
    (Spec (.of k)) X X a
  let : IsAffine Z.left := hZ
  obtain ⟨d, c, m, hc, H⟩ := multiplicativeGroup_roof_monomial k Ω p Z s f hs
  refine ⟨d, c, m, hc, ?_⟩
  intro z
  have hbij := (isIso_iff_bijective _).mp
    (schemePointsFunctor_invertsUH (fieldGeometricPoint k Ω) s hs)
  obtain ⟨l, hl⟩ := hbij.surjective (multiplicativeGroupRelativePoint k Ω z)
  have hact := congrArg (fun g ↦ F.map g) ha
  rw [Functor.map_comp, localizedSchemePoints_map, localizedSchemePoints_map] at hact
  have hl' : l.val ≫ s.left = multiplicativeGroupPoint k Ω z := congrArg Subtype.val hl
  have hf : F.map a (multiplicativeGroupRelativePoint k Ω z) =
      (schemePointsFunctor (fieldGeometricPoint k Ω)).map f l := by
    have he := congrArg (fun g ↦ g l) hact
    change F.map a ((schemePointsFunctor (fieldGeometricPoint k Ω)).map s l) = _ at he
    rwa [hl] at he
  rw [hf]
  exact H l.val z hl'

end EtaleCounterexample
