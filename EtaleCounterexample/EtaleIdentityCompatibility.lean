import EtaleCounterexample.AffineTargetEtale
import EtaleCounterexample.LocalizedEtaleComposition

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u

/-- The actual direct image of the identity scheme map has the identity
relative comparison, including the canonical site unit isomorphism. -/
theorem relativeAffineEtaleIdentity {S : Scheme.{u}} {R : CommRingCat.{u}}
    (π : Spec R ⟶ S) :
    RelativeCompatible (relativeAffineEtaleMorphism (𝟙 _) π π (Category.id_comp _))
      (identityTwist (etaleDirectImage π) (Iso.refl _)) (etaleDirectImageIdIso _) := by
  intro M
  change (etaleDirectImage π).map ((etaleDirectImageIdIso _).hom.app M) ≫ 𝟙 _ =
    (etaleDirectImageCompIsoOfEq (𝟙 _) π (Category.id_comp _)).hom.app M
  rw [Category.comp_id]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  obtain ⟨U⟩ := U
  change ((etaleDirectImageIdIso _).hom.app M).hom.app (op ((etaleBaseChange π).obj U)) = _
  rw [etaleDirectImageCompIsoOfEq_app]
  change M.obj.map (((etaleBaseChangeIdIso _).inv.app ((etaleBaseChange π).obj U)).op) = _
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.fst ((etaleBaseChange π).obj U).hom (𝟙 _))).mp
  simp [etaleBaseChangeIdIso, MorphismProperty.Over.pullbackComp, etaleBaseChange]
  apply pullback.hom_ext <;> simp

variable (k : Type u) [Field k]

theorem ordinaryGmEndomorphism_isInduced
    (f : multiplicativeGroupFiniteType k ⟶ multiplicativeGroupFiniteType k) :
    IsInducedByLocalizedEndomorphism k ((relativeUH _).Q.map f)
      (relativeMultiplicativeGroupMorphism k (multiplicativeGroupFiniteType k) f) := by
  let r : MultiplicativeGroupLocalizedRoof k ((relativeUH _).Q.map f) := {
    source := multiplicativeGroupFiniteType k
    denominator := 𝟙 _
    numerator := f
    isUH := (relativeUH _).id_mem _
    represents := by simp }
  let F := relativeMultiplicativeGroupMorphism k (multiplicativeGroupFiniteType k) f
  exact ⟨r, _, ((relativeAffineEtaleIdentity (multiplicativeGroupStructure k)).whiskerRight F).trans
    (relativeCompatible_leftUnitor F)⟩

theorem localizedEtaleEndomorphism_map (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : multiplicativeGroupFiniteType k ⟶ multiplicativeGroupFiniteType k) :
    RelativelyIsomorphic (localizedEtaleEndomorphism k p ((relativeUH _).Q.map f))
      (relativeMultiplicativeGroupMorphism k (multiplicativeGroupFiniteType k) f) :=
  localizedEtaleRealization_unique k p _ _ _ (localizedRoof_etaleMorphism_isInduced k p _)
    (ordinaryGmEndomorphism_isInduced k f)

end EtaleCounterexample
