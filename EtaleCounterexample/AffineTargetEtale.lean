import EtaleCounterexample.AffineUHInvariance
import EtaleCounterexample.EtaleCoherence

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u

def equivalentEtaleMorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(etaleDirectImage f).IsEquivalence] : GeometricMorphism (EtaleTopos X) (EtaleTopos Y) where
  inverseImage := (etaleDirectImage f).inv
  directImage := etaleDirectImage f
  adjunction := (etaleDirectImage f).asEquivalence.symm.toAdjunction
  leftExact := inferInstance

/-- The actual geometric morphism for any affine target, without requiring
that the chosen presentation of the target is definitionally a Spec. -/
def affineTargetEtaleMorphism {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    GeometricMorphism (EtaleTopos X) (EtaleTopos Y) := by
  let G := (affineBaseEtaleMorphism (f ≫ Y.isoSpec.hom)).comp
    (equivalentEtaleMorphism Y.isoSpec.inv)
  let e : G.directImage ≅ etaleDirectImage f :=
    etaleDirectImageCompIsoOfEq _ _ (by simp)
  exact {
    inverseImage := G.inverseImage
    directImage := etaleDirectImage f
    adjunction := G.adjunction.ofNatIsoRight e
    leftExact := G.leftExact }

@[simp] theorem affineTargetEtaleMorphism_directImage {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) : (affineTargetEtaleMorphism f).directImage = etaleDirectImage f := rfl

def relativeAffineTargetEtaleMorphism {X Y S : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (π : X ⟶ S) (ρ : Y ⟶ S) (hf : f ≫ ρ = π) :
    RelativeMorphism (etaleDirectImage π) (etaleDirectImage ρ) where
  geometric := affineTargetEtaleMorphism f
  comparison := etaleDirectImageCompIsoOfEq f ρ hf

/-- Composition is compatible with the structural comparisons; no inference
from agreement on points enters this statement. -/
theorem relativeAffineTargetEtaleMorphism_comp {X Y Z S : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (π : X ⟶ S) (ρ : Y ⟶ S) (σ : Z ⟶ S)
    (hf : f ≫ ρ = π) (hg : g ≫ σ = ρ) (hfg : f ≫ g = fg) (hfgσ : fg ≫ σ = π) :
    RelativeCompatible
      ((relativeAffineTargetEtaleMorphism f π ρ hf).comp
        (relativeAffineTargetEtaleMorphism g ρ σ hg))
      (relativeAffineTargetEtaleMorphism fg π σ hfgσ)
      (etaleDirectImageCompIsoOfEq f g hfg) := by
  intro M
  simpa [RelativeMorphism.comp, relativeAffineTargetEtaleMorphism, GeometricMorphism.comp]
    using etaleDirectImage_composition_coherence f g σ fg π ρ hfg hg hf hfgσ M

/-- Agreement with the earlier affine-Spec construction, including its
structural comparison. Different choices of left adjoint do not change the
relative direct-image isomorphism class. -/
theorem relativeAffineTargetEtaleMorphism_spec {X S : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (π : X ⟶ S) (ρ : Spec R ⟶ S) (hf : f ≫ ρ = π) :
    RelativeCompatible (relativeAffineTargetEtaleMorphism f π ρ hf)
      (relativeAffineEtaleMorphism f π ρ hf) (Iso.refl _) := by
  intro M
  change (etaleDirectImage ρ).map (𝟙 _) ≫ _ = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end EtaleCounterexample
