import EtaleCounterexample.RelativeIsoCalculus

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅
variable {E : Type u₁} {D : Type u₂} {A : Type u₃} {B : Type u₄} {C : Type u₅}
  [Category.{v₁} E] [Category.{v₂} D] [Category.{v₃} A]
  [Category.{v₄} B] [Category.{v₅} C]

/-- Transport a commuting triangle through two specified comparison squares. -/
theorem relativeTriangle_transport {ρ ρ' : E ⥤ B} (eρ : ρ ≅ ρ')
    {x y : E} {b b' : B} (c : ρ.obj x ⟶ b) (d : ρ.obj y ⟶ b)
    (c' : ρ'.obj x ⟶ b') (d' : ρ'.obj y ⟶ b') (e : b ⟶ b')
    (hc : c ≫ e = eρ.hom.app x ≫ c') (hd : d ≫ e = eρ.hom.app y ≫ d')
    (γ : x ⟶ y) (hγ : ρ.map γ ≫ d = c) : ρ'.map γ ≫ d' = c' := by
  apply (cancel_epi (eρ.hom.app x)).mp
  rw [← Category.assoc, ← eρ.hom.naturality, Category.assoc, ← hd,
    ← Category.assoc, hγ, hc]

/-- Change the relative base by an actual direct-image functor. -/
def RelativeMorphism.postcompose {π : E ⥤ B} {ρ : D ⥤ B}
    (f : RelativeMorphism π ρ) (J : B ⥤ C) : RelativeMorphism (π ⋙ J) (ρ ⋙ J) where
  geometric := f.geometric
  comparison := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight f.comparison J

theorem RelativeCompatible.postcompose {π : E ⥤ B} {ρ : D ⥤ B}
    {f h : RelativeMorphism π ρ}
    {γ : f.geometric.directImage ≅ h.geometric.directImage}
    (hγ : RelativeCompatible f h γ) (J : B ⥤ C) :
    RelativeCompatible (f.postcompose J) (h.postcompose J) γ := by
  intro M
  simpa [RelativeMorphism.postcompose] using congrArg J.map (hγ M)

theorem relativeCompatible_postcompose_comp {π : E ⥤ B} {ρ : D ⥤ B} {σ : A ⥤ B}
    (f : RelativeMorphism π ρ) (g : RelativeMorphism ρ σ) (J : B ⥤ C) :
    RelativeCompatible ((f.postcompose J).comp (g.postcompose J))
      ((f.comp g).postcompose J) (Iso.refl _) := by
  intro M
  simp [RelativeMorphism.comp, RelativeMorphism.postcompose, GeometricMorphism.comp]

theorem postcompose_isRelativeEquivalence {π : E ⥤ B} {ρ : D ⥤ B}
    (f : RelativeMorphism π ρ) (hf : IsRelativeEquivalence f) (J : B ⥤ C) :
    IsRelativeEquivalence (f.postcompose J) := by
  obtain ⟨g, ⟨γ, hγ⟩, ⟨δ, hδ⟩⟩ := hf
  refine ⟨g.postcompose J, ⟨γ, ?_⟩, ⟨δ, ?_⟩⟩
  · have H := (relativeCompatible_postcompose_comp f g J).trans (hγ.postcompose J)
    intro M
    simpa [RelativeMorphism.comp, RelativeMorphism.postcompose, identityTwist,
      GeometricMorphism.id, GeometricMorphism.comp] using H M
  · have H := (relativeCompatible_postcompose_comp g f J).trans (hδ.postcompose J)
    intro M
    simpa [RelativeMorphism.comp, RelativeMorphism.postcompose, identityTwist,
      GeometricMorphism.id, GeometricMorphism.comp] using H M

/-- Reidentify structural functors by specified natural isomorphisms. -/
def RelativeMorphism.changeStructure {π π' : E ⥤ B} {ρ ρ' : D ⥤ B}
    (f : RelativeMorphism π ρ) (eπ : π ≅ π') (eρ : ρ ≅ ρ') :
    RelativeMorphism π' ρ' where
  geometric := f.geometric
  comparison := isoWhiskerLeft _ eρ.symm ≪≫ f.comparison ≪≫ eπ

theorem RelativeCompatible.changeStructure {π π' : E ⥤ B} {ρ ρ' : D ⥤ B}
    {f h : RelativeMorphism π ρ} {γ : f.geometric.directImage ≅ h.geometric.directImage}
    (hγ : RelativeCompatible f h γ) (eπ : π ≅ π') (eρ : ρ ≅ ρ') :
    RelativeCompatible (f.changeStructure eπ eρ) (h.changeStructure eπ eρ) γ := by
  intro M
  dsimp [RelativeMorphism.changeStructure]
  rw [← Category.assoc, ← Category.assoc, eρ.inv.naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (ρ.map (γ.hom.app M)), hγ M]

end EtaleCounterexample
