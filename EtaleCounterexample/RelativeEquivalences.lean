import EtaleCounterexample.NonintegralTwist

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
variable {E : Type u₁} {D : Type u₂} {A : Type u₃} {B : Type u₄}
  [Category.{v₁} E] [Category.{v₂} D] [Category.{v₃} A] [Category.{v₄} B]

/-- Composition of actual adjunctions with left exact inverse images. -/
def GeometricMorphism.comp (f : GeometricMorphism E D) (g : GeometricMorphism D A) :
    GeometricMorphism E A where
  inverseImage := g.inverseImage ⋙ f.inverseImage
  directImage := f.directImage ⋙ g.directImage
  adjunction := g.adjunction.comp f.adjunction
  leftExact := by
    let := f.leftExact
    let := g.leftExact
    infer_instance

/-- Composition with the genuine relative comparison convention. -/
def RelativeMorphism.comp {π : E ⥤ B} {ρ : D ⥤ B} {σ : A ⥤ B}
    (f : RelativeMorphism π ρ) (g : RelativeMorphism ρ σ) : RelativeMorphism π σ where
  geometric := f.geometric.comp g.geometric
  comparison := associator _ _ _ ≪≫ isoWhiskerLeft _ g.comparison ≪≫ f.comparison

/-- A two-sided inverse, witnessed by the two actual relative triangles. -/
def IsRelativeEquivalence {π : E ⥤ B} {ρ : D ⥤ B} (f : RelativeMorphism π ρ) : Prop :=
  ∃ g : RelativeMorphism ρ π,
    (∃ γ : (f.comp g).geometric.directImage ≅ 𝟭 E,
      RelativeCompatible (f.comp g) (identityTwist π (Iso.refl _)) γ) ∧
    (∃ γ : (g.comp f).geometric.directImage ≅ 𝟭 D,
      RelativeCompatible (g.comp f) (identityTwist ρ (Iso.refl _)) γ)

/-- Identity twists are genuine relative equivalences, with inverse comparison. -/
theorem identityTwist_isRelativeEquivalence (π : E ⥤ B) (η : 𝟭 B ≅ 𝟭 B) :
    IsRelativeEquivalence (identityTwist π η) := by
  refine ⟨identityTwist π η.symm, ⟨(𝟭 E).leftUnitor, ?_⟩,
    ⟨(𝟭 E).leftUnitor, ?_⟩⟩
  all_goals
    intro X
    simp [RelativeMorphism.comp, GeometricMorphism.comp, identityTwist,
      GeometricMorphism.id]

universe u

/-- The point twist used in the explicit sign calculation is the actual
composition with an identity twist, with the identity-functor unitor included. -/
theorem relativeEtalePoint_comp_identityTwist
    {X Y : AlgebraicGeometry.Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f : X ⟶ Y) (s : AlgebraicGeometry.Spec (.of Ω) ⟶ X)
    {ω : AlgebraicGeometry.Spec (.of Ω) ⟶ Y} (hs : s ≫ f = ω)
    (η : 𝟭 (EtaleTopos Y) ≅ 𝟭 (EtaleTopos Y)) :
    RelativeCompatible
      ((relativeEtalePoint f s hs).comp (identityTwist (etaleDirectImage f) η))
      (twistRelativeEtalePoint f s hs η)
      ((etalePoint s).directImage.rightUnitor) := by
  intro M
  simp [RelativeMorphism.comp, relativeEtalePoint, twistRelativeEtalePoint,
    identityTwist, GeometricMorphism.comp, GeometricMorphism.id]

variable (k : Type u) [Field k] [Fintype k]

/-- The actual selected nonintegral twist is relatively invertible. -/
theorem nonintegralTwist_isRelativeEquivalence {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) :
    IsRelativeEquivalence (nonintegralTwist k f) :=
  identityTwist_isRelativeEquivalence _ _

/-- Its underlying geometric morphism is literally the identity. -/
theorem nonintegralTwist_underlying_identity {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) :
    (nonintegralTwist k f).geometric = GeometricMorphism.id (EtaleTopos X) := rfl

end EtaleCounterexample
