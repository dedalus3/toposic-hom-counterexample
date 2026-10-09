import EtaleCounterexample.RelativeEquivalences

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅
variable {A : Type u₁} {E : Type u₂} {D : Type u₃} {C : Type u₄} {B : Type u₅}
  [Category.{v₁} A] [Category.{v₂} E] [Category.{v₃} D] [Category.{v₄} C] [Category.{v₅} B]
  {σ : A ⥤ B} {π : E ⥤ B} {ρ : D ⥤ B} {τ : C ⥤ B}

theorem RelativeCompatible.refl (f : RelativeMorphism π ρ) :
    RelativeCompatible f f (Iso.refl _) := by intro X; simp

theorem RelativeCompatible.symm {f g : RelativeMorphism π ρ}
    {γ : f.geometric.directImage ≅ g.geometric.directImage}
    (hγ : RelativeCompatible f g γ) : RelativeCompatible g f γ.symm := by
  intro X
  apply (cancel_epi (ρ.map (γ.hom.app X))).mp
  simp only [Iso.symm_hom, ← Category.assoc, ← map_comp, γ.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (hγ X).symm

theorem RelativeCompatible.trans {f g h : RelativeMorphism π ρ}
    {γ : f.geometric.directImage ≅ g.geometric.directImage}
    {δ : g.geometric.directImage ≅ h.geometric.directImage}
    (hγ : RelativeCompatible f g γ) (hδ : RelativeCompatible g h δ) :
    RelativeCompatible f h (γ ≪≫ δ) := by
  intro X
  dsimp
  rw [map_comp, Category.assoc, hδ X, hγ X]

theorem RelativeCompatible.whiskerLeft (a : RelativeMorphism σ π)
    {f g : RelativeMorphism π ρ}
    {γ : f.geometric.directImage ≅ g.geometric.directImage}
    (hγ : RelativeCompatible f g γ) :
    RelativeCompatible (a.comp f) (a.comp g)
      (isoWhiskerLeft a.geometric.directImage γ) := by
  intro X
  simpa [RelativeMorphism.comp, GeometricMorphism.comp] using
    congrArg (fun t ↦ t ≫ a.comparison.hom.app X) (hγ (a.geometric.directImage.obj X))

theorem RelativeCompatible.whiskerRight {f g : RelativeMorphism π ρ}
    {γ : f.geometric.directImage ≅ g.geometric.directImage}
    (hγ : RelativeCompatible f g γ) (a : RelativeMorphism ρ τ) :
    RelativeCompatible (f.comp a) (g.comp a)
      (isoWhiskerRight γ a.geometric.directImage) := by
  intro X
  have H := a.comparison.hom.naturality (γ.hom.app X)
  dsimp [RelativeMorphism.comp, GeometricMorphism.comp]
  dsimp at H
  simp only [Category.id_comp, ← Category.assoc]
  rw [H, Category.assoc, hγ X]

theorem relativeCompatible_associator (a : RelativeMorphism σ π)
    (f : RelativeMorphism π ρ) (g : RelativeMorphism ρ τ) :
    RelativeCompatible ((a.comp f).comp g) (a.comp (f.comp g))
      (associator _ _ _) := by
  intro X
  simp [RelativeMorphism.comp, GeometricMorphism.comp]

theorem relativeCompatible_leftUnitor (f : RelativeMorphism π ρ) :
    RelativeCompatible ((identityTwist π (Iso.refl _)).comp f) f
      f.geometric.directImage.leftUnitor := by
  intro X
  simp [RelativeMorphism.comp, GeometricMorphism.comp, identityTwist, GeometricMorphism.id]

theorem relativeCompatible_rightUnitor (f : RelativeMorphism π ρ) :
    RelativeCompatible (f.comp (identityTwist ρ (Iso.refl _))) f
      f.geometric.directImage.rightUnitor := by
  intro X
  simp [RelativeMorphism.comp, GeometricMorphism.comp, identityTwist, GeometricMorphism.id]

/-- The inverse of a relative geometric morphism whose actual direct image is
an equivalence, with its structural comparison fixed by the original one. -/
def RelativeMorphism.equivalenceInverse (f : RelativeMorphism π ρ)
    [f.geometric.directImage.IsEquivalence] : RelativeMorphism ρ π where
  geometric := {
    inverseImage := f.geometric.directImage
    directImage := f.geometric.directImage.inv
    adjunction := f.geometric.directImage.asEquivalence.toAdjunction
    leftExact := inferInstance }
  comparison := isoWhiskerLeft f.geometric.directImage.inv f.comparison.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight f.geometric.directImage.asEquivalence.counitIso ρ ≪≫ ρ.leftUnitor

theorem relativeCompatible_inverse_comp (f : RelativeMorphism π ρ)
    [f.geometric.directImage.IsEquivalence] :
    RelativeCompatible (f.equivalenceInverse.comp f) (identityTwist ρ (Iso.refl _))
      f.geometric.directImage.asEquivalence.counitIso := by
  intro X
  simp [RelativeMorphism.comp, RelativeMorphism.equivalenceInverse,
    GeometricMorphism.comp, identityTwist, GeometricMorphism.id]

theorem relativeCompatible_comp_inverse (f : RelativeMorphism π ρ)
    [f.geometric.directImage.IsEquivalence] :
    RelativeCompatible (f.comp f.equivalenceInverse) (identityTwist π (Iso.refl _))
      f.geometric.directImage.asEquivalence.unitIso.symm := by
  intro X
  dsimp [RelativeMorphism.comp, RelativeMorphism.equivalenceInverse,
    GeometricMorphism.comp, identityTwist, GeometricMorphism.id]
  simp only [Category.comp_id, Category.id_comp]
  have H := f.comparison.inv.naturality
    (f.geometric.directImage.asEquivalence.unitIso.inv.app X)
  dsimp at H
  erw [f.geometric.directImage.asEquivalence.counit_app_functor]
  erw [← H]
  simp only [Category.assoc, f.comparison.inv_hom_id_app, Category.comp_id]

end EtaleCounterexample
