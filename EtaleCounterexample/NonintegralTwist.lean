import EtaleCounterexample.NonintegralSite
import EtaleCounterexample.MultiplicativeGroupPoints

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω]

def nonintegralSpecAutomorphism : Spec (.of Ω) ≅ Spec (.of Ω) :=
  algebraAutomorphismSpec k Ω (nonintegralFieldAutomorphism k Ω)

theorem nonintegralSpecAutomorphism_over :
    (nonintegralSpecAutomorphism k Ω).hom ≫ fieldGeometricPoint k Ω =
      fieldGeometricPoint k Ω :=
  algebraAutomorphismSpec_over k Ω _

variable [IsSepClosed Ω]

theorem nonintegral_lift_commutes (A : CommAlgCat.FiniteEtale.{u} k)
    (l : (Scheme.pointSmallEtale (fieldGeometricPoint k Ω)).fiber.obj
      (finiteEtaleScheme k (op A))) :
    (nonintegralSpecAutomorphism k Ω).hom ≫ l.left =
      l.left ≫ Spec.map (CommRingCat.ofHom (finiteEtaleNonintegralAutomorphism k A).toRingHom) := by
  obtain ⟨a, rfl⟩ := (finiteEtaleLiftEquiv k Ω A).symm.surjective l
  change Spec.map (CommRingCat.ofHom (nonintegralFieldAutomorphism k Ω).toRingHom) ≫
    Spec.map (CommRingCat.ofHom a.toRingHom) =
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (finiteEtaleNonintegralAutomorphism k A).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact nonintegralAutomorphism_fiber k Ω A a x

omit [IsSepClosed Ω] in
theorem nonintegralToposIso_restrict (P : EtaleTopos (Spec (.of k)))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    ((nonintegralToposIso k).hom.app P).hom.app (op (finiteEtaleScheme k A)) =
      P.obj.map (((finiteEtaleSpec k ⋙ Scheme.AffineEtale.Spec _).map
        ((nonintegralSiteIso k).hom.app A)).op) := by
  have h := transportIdentityIso_inverse_map (finiteEtaleSheafEquivalence k)
    (siteIdentityAction (finiteEtaleTopology k) (nonintegralSiteIso k)) P
  have h' := congrArg (fun m ↦ m.hom.app (op A)) h
  rw [siteIdentityAction_component] at h'
  exact h'

/-- The actual base-mate equation for the selected nonintegral automorphism. -/
theorem nonintegralPointMate_eq_toposIso (M : Type u) :
    (etalePointRightMateOfEq (nonintegralSpecAutomorphism k Ω)
      (nonintegralSpecAutomorphism_over k Ω)).hom.app M =
    (nonintegralToposIso k).hom.app
      ((etalePoint (fieldGeometricPoint k Ω)).directImage.obj M) := by
  apply (finiteEtaleSheafEquivalence k).inverse.map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext A
  change ((etalePointRightMateOfEq (nonintegralSpecAutomorphism k Ω)
    (nonintegralSpecAutomorphism_over k Ω)).hom.app M).hom.app
      (op (finiteEtaleScheme k A.unop)) =
    ((nonintegralToposIso k).hom.app
      ((etalePoint (fieldGeometricPoint k Ω)).directImage.obj M)).hom.app
        (op (finiteEtaleScheme k A.unop))
  rw [nonintegralToposIso_restrict]
  apply Pi.hom_ext
  intro l
  rw [etalePointRightMateOfEq_projection]
  change Pi.π _ _ = Pi.map' (f := fun _ ↦ M) (g := fun _ ↦ M) _ (fun _ ↦ 𝟙 M) ≫ Pi.π _ l
  rw [Pi.map'_comp_π, Category.comp_id]
  congr 1
  apply CategoryTheory.Over.OverMorphism.ext
  exact nonintegral_lift_commutes k Ω A.unop.unop l

/-- The actual nonintegral relative twist. Its comparison is the inverse of
the base action, as required for the positive action on relative points. -/
def nonintegralTwist {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    RelativeMorphism (etaleDirectImage f) (etaleDirectImage f) :=
  identityTwist (etaleDirectImage f) (nonintegralToposIso k).symm

theorem nonintegral_relativePointAction {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (s : Spec (.of Ω) ⟶ X)
    (hs : s ≫ f = fieldGeometricPoint k Ω) :
    RelativeCompatible
      (twistRelativeEtalePoint f s hs (nonintegralToposIso k).symm)
      (relativeEtalePoint f ((nonintegralSpecAutomorphism k Ω).hom ≫ s)
        (show ((nonintegralSpecAutomorphism k Ω).hom ≫ s) ≫ f =
            fieldGeometricPoint k Ω by
          rw [Category.assoc, hs, nonintegralSpecAutomorphism_over]))
      (etalePointRightMateOfEq (nonintegralSpecAutomorphism k Ω) rfl).symm :=
  relativePointAction_of_baseEquation (nonintegralSpecAutomorphism k Ω) f s hs
    (nonintegralSpecAutomorphism_over k Ω) (nonintegralToposIso k)
    (nonintegralPointMate_eq_toposIso k Ω)

/-- The full coordinate statement, with an actual relative isomorphism:
`T_a(x_z)` is relatively isomorphic to `x_(σ z)` for the chosen compatible a. -/
theorem multiplicativeGroup_nonintegral_relativePointAction (z : Ωˣ) :
    ∃ γ : (etalePoint (multiplicativeGroupPoint k Ω z)).directImage ≅
        (etalePoint (multiplicativeGroupPoint k Ω
          (Units.map (nonintegralFieldAutomorphism k Ω).toMonoidHom z))).directImage,
      RelativeCompatible
        (twistRelativeEtalePoint (multiplicativeGroupStructure k)
          (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)
          (nonintegralToposIso k).symm)
        (relativeEtalePoint (multiplicativeGroupStructure k)
          (multiplicativeGroupPoint k Ω
            (Units.map (nonintegralFieldAutomorphism k Ω).toMonoidHom z))
          (multiplicativeGroupPoint_over k Ω _)) γ := by
  have ht : ((nonintegralSpecAutomorphism k Ω).hom ≫ multiplicativeGroupPoint k Ω z) ≫
      multiplicativeGroupStructure k = fieldGeometricPoint k Ω := by
    rw [Category.assoc, multiplicativeGroupPoint_over, nonintegralSpecAutomorphism_over]
  have H : ∃ γ : (etalePoint (multiplicativeGroupPoint k Ω z)).directImage ≅
        (etalePoint ((nonintegralSpecAutomorphism k Ω).hom ≫
          multiplicativeGroupPoint k Ω z)).directImage,
      RelativeCompatible
        (twistRelativeEtalePoint (multiplicativeGroupStructure k)
          (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)
          (nonintegralToposIso k).symm)
        (relativeEtalePoint (multiplicativeGroupStructure k)
          ((nonintegralSpecAutomorphism k Ω).hom ≫ multiplicativeGroupPoint k Ω z) ht) γ :=
    ⟨_, nonintegral_relativePointAction k Ω _ _ (multiplicativeGroupPoint_over k Ω z)⟩
  revert H ht
  have hcoord : (nonintegralSpecAutomorphism k Ω).hom ≫ multiplicativeGroupPoint k Ω z =
      multiplicativeGroupPoint k Ω
        (Units.map (nonintegralFieldAutomorphism k Ω).toMonoidHom z) :=
    multiplicativeGroupPoint_automorphism k Ω (nonintegralFieldAutomorphism k Ω) z
  rw [hcoord]
  intro ht H
  exact H

end EtaleCounterexample
