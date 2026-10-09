import EtaleCounterexample.FiniteFieldBaseTwist
import EtaleCounterexample.FiniteEtaleFibers

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Field Ω] [IsSepClosed Ω] [Algebra k Ω]

def algebraAutomorphismSpec (σ : Ω ≃ₐ[k] Ω) : Spec (.of Ω) ≅ Spec (.of Ω) :=
  Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op

omit [IsSepClosed Ω] in
theorem algebraAutomorphismSpec_over (σ : Ω ≃ₐ[k] Ω) :
    (algebraAutomorphismSpec k Ω σ).hom ≫ fieldGeometricPoint k Ω =
      fieldGeometricPoint k Ω := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k Ω)) = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext σ.toAlgHom.comp_algebraMap

variable [Fintype k] [Algebra.IsAlgebraic k Ω]

def arithmeticFrobeniusSpec : Spec (.of Ω) ≅ Spec (.of Ω) :=
  algebraAutomorphismSpec k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

omit [IsSepClosed Ω] in
theorem arithmeticFrobeniusSpec_over :
    (arithmeticFrobeniusSpec k Ω).hom ≫ fieldGeometricPoint k Ω =
      fieldGeometricPoint k Ω :=
  algebraAutomorphismSpec_over k Ω _

theorem finiteEtaleFrobenius_lift_commutes (A : CommAlgCat.FiniteEtale.{u} k)
    (l : (Scheme.pointSmallEtale (fieldGeometricPoint k Ω)).fiber.obj
      (finiteEtaleScheme k (op A))) :
    (arithmeticFrobeniusSpec k Ω).hom ≫ l.left =
      l.left ≫ Spec.map (CommRingCat.ofHom (finiteEtaleFrobenius k A).toRingHom) := by
  obtain ⟨a, rfl⟩ := (finiteEtaleLiftEquiv k Ω A).symm.surjective l
  change Spec.map (CommRingCat.ofHom
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toRingHom) ≫
    Spec.map (CommRingCat.ofHom a.toRingHom) =
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (finiteEtaleFrobenius k A).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact (map_pow a x (Fintype.card k)).symm

theorem finiteFieldFrobeniusToposIso_restrict (P : EtaleTopos (Spec (.of k)))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    ((finiteFieldFrobeniusToposIso k).hom.app P).hom.app (op (finiteEtaleScheme k A)) =
      P.obj.map (((finiteEtaleSpec k ⋙ Scheme.AffineEtale.Spec _).map
        ((finiteEtaleFrobeniusSiteIso k).hom.app A)).op) := by
  have h := transportIdentityIso_inverse_map (finiteEtaleSheafEquivalence k)
    (siteIdentityAction (finiteEtaleTopology k) (finiteEtaleFrobeniusSiteIso k)) P
  have h' := congrArg (fun m ↦ m.hom.app (op A)) h
  rw [siteIdentityAction_component] at h'
  exact h'

/-- The base equation for arithmetic Frobenius on actual étale sheaves.
The right mate equals the actual topos automorphism constructed from Frobenius,
not merely a transformation with matching point values. -/
theorem frobeniusPointMate_eq_toposIso (M : Type u) :
    (etalePointRightMateOfEq (arithmeticFrobeniusSpec k Ω)
      (arithmeticFrobeniusSpec_over k Ω)).hom.app M =
    (finiteFieldFrobeniusToposIso k).hom.app
      ((etalePoint (fieldGeometricPoint k Ω)).directImage.obj M) := by
  apply (finiteEtaleSheafEquivalence k).inverse.map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext A
  change ((etalePointRightMateOfEq (arithmeticFrobeniusSpec k Ω)
    (arithmeticFrobeniusSpec_over k Ω)).hom.app M).hom.app
      (op (finiteEtaleScheme k A.unop)) =
    ((finiteFieldFrobeniusToposIso k).hom.app
      ((etalePoint (fieldGeometricPoint k Ω)).directImage.obj M)).hom.app
        (op (finiteEtaleScheme k A.unop))
  rw [finiteFieldFrobeniusToposIso_restrict]
  apply Pi.hom_ext
  intro l
  rw [etalePointRightMateOfEq_projection]
  change Pi.π _ _ = Pi.map' (f := fun _ ↦ M) (g := fun _ ↦ M) _ (fun _ ↦ 𝟙 M) ≫ Pi.π _ l
  rw [Pi.map'_comp_π, Category.comp_id]
  congr 1
  apply CategoryTheory.Over.OverMorphism.ext
  exact finiteEtaleFrobenius_lift_commutes k Ω A.unop.unop l

end EtaleCounterexample
