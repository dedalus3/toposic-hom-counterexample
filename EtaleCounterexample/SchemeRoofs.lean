import EtaleCounterexample.UniversalHomeomorphisms
import EtaleCounterexample.LocalizationRoofs
import Mathlib.AlgebraicGeometry.Noetherian

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (S : Scheme.{u}) [IsNoetherian S]

instance finiteTypeSource_isNoetherian (X : FiniteTypeSchemes S) : IsNoetherian X.left := by
  have : LocallyOfFiniteType X.hom := X.prop.1
  have : QuasiCompact X.hom := X.prop.2
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian (Y := S) X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace (Y := S) X.hom
  constructor

/-- Over a Noetherian base, every morphism between the finite-type objects is
itself of finite type. This supplies finite type of the intermediate roof. -/
theorem finiteTypeScheme_hom_finiteType {X Y : FiniteTypeSchemes S} (f : X ⟶ Y) :
    finiteType f.left := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := f.w.symm ▸ X.prop.1
  exact ⟨locallyOfFiniteType_of_comp f.left Y.hom, inferInstance⟩

theorem relativeUH_ore {X Y T : FiniteTypeSchemes S}
    (f : X ⟶ T) (s : Y ⟶ T) (hs : relativeUH S s) :
    ∃ (P : FiniteTypeSchemes S) (r : P ⟶ X) (t : P ⟶ Y),
      relativeUH S r ∧ r ≫ f = t ≫ s := by
  have hsft := finiteTypeScheme_hom_finiteType S s
  have hfst : finiteType (pullback.fst f.left s.left) :=
    finiteType.pullback_fst f.left s.left hsft
  let P : FiniteTypeSchemes S := MorphismProperty.Over.mk ⊤
    (pullback.fst f.left s.left ≫ X.hom)
    (finiteType.comp_mem _ _ hfst X.prop)
  let r : P ⟶ X := MorphismProperty.Over.homMk (pullback.fst f.left s.left) rfl trivial
  let t : P ⟶ Y := MorphismProperty.Over.homMk (pullback.snd f.left s.left) (by
    change pullback.snd f.left s.left ≫ Y.hom = pullback.fst f.left s.left ≫ X.hom
    rw [← show f.left ≫ T.hom = X.hom from by simp,
      ← show s.left ≫ T.hom = Y.hom from by simp]
    simp only [← Category.assoc, pullback.condition]) trivial
  refine ⟨P, r, t, ?_, ?_⟩
  · exact universalHomeomorphisms.pullback_fst f.left s.left hs
  · ext
    exact pullback.condition

/-- Every actual localized morphism, including arbitrary zigzags, has a
finite-type universal-homeomorphism roof. -/
theorem localizedScheme_morphism_has_roof (X Y : FiniteTypeSchemes S)
    (a : (relativeUH S).Q.obj X ⟶ (relativeUH S).Q.obj Y) :
    ∃ (Z : FiniteTypeSchemes S) (s : Z ⟶ X) (f : Z ⟶ Y),
      relativeUH S s ∧ (relativeUH S).Q.map s ≫ a = (relativeUH S).Q.map f :=
  every_localized_morphism_has_roof (relativeUH S) (fun f s hs ↦ relativeUH_ore S f s hs) X Y a

/-- For an affine source, the denominator's source is affine as well. -/
theorem localizedScheme_morphism_has_affine_roof (X Y : FiniteTypeSchemes S)
    [IsAffine X.left] (a : (relativeUH S).Q.obj X ⟶ (relativeUH S).Q.obj Y) :
    ∃ (Z : FiniteTypeSchemes S) (s : Z ⟶ X) (f : Z ⟶ Y),
      IsAffine Z.left ∧ relativeUH S s ∧
        (relativeUH S).Q.map s ≫ a = (relativeUH S).Q.map f := by
  obtain ⟨Z, s, f, hs, h⟩ := localizedScheme_morphism_has_roof S X Y a
  have : IsAffineHom s.left :=
    isAffineHom_of_homeomorph s.left (universalHomeomorphism_homeomorph s.left hs)
  exact ⟨Z, s, f, isAffine_of_isAffineHom s.left, hs, h⟩

end EtaleCounterexample
