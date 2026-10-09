import EtaleCounterexample.EtaleCoherence
import EtaleCounterexample.RelativeBaseChange

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
namespace EtaleCounterexample
universe u

/-- Postcomposing a scheme-induced relative geometric morphism with a change
of base gives the actual scheme-induced morphism over the composite base.
Both structural identifications are the canonical étale pullback comparisons. -/
theorem relativeAffineEtaleMorphism_postcompose
    {X Y Z : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (π : X ⟶ Y) (ρ : Spec R ⟶ Y)
    (hf : f ≫ ρ = π) (i : Y ⟶ Z) (π' : X ⟶ Z) (hπ : π ≫ i = π') :
    RelativeCompatible
      (((relativeAffineEtaleMorphism f π ρ hf).postcompose (etaleDirectImage i)).changeStructure
        (etaleDirectImageCompIsoOfEq π i hπ) (etaleDirectImageCompIso ρ i))
      (relativeAffineEtaleMorphism f π' (ρ ≫ i)
        (by rw [← Category.assoc, hf, hπ])) (Iso.refl _) := by
  intro M
  change (etaleDirectImage (ρ ≫ i)).map (𝟙 _) ≫
      (etaleDirectImageCompIsoOfEq f (ρ ≫ i) (by rw [← Category.assoc, hf, hπ])).hom.app M = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_epi ((etaleDirectImageCompIso ρ i).hom.app ((etaleDirectImage f).obj M))).mp
  have H := etaleDirectImage_composition_coherence f ρ i π π' (ρ ≫ i) hf rfl
    (by rw [← Category.assoc, hf, hπ]) hπ M
  dsimp [RelativeMorphism.changeStructure, RelativeMorphism.postcompose,
    relativeAffineEtaleMorphism]
  simp only [Category.id_comp, ← Category.assoc, affineBaseEtaleMorphism,
    Iso.hom_inv_id_app, Category.id_comp]
  simpa [etaleDirectImageCompIsoOfEq] using H.symm

end EtaleCounterexample
