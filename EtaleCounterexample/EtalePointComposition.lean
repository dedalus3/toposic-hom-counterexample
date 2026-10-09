import EtaleCounterexample.EtaleComposition
import EtaleCounterexample.RelativeFiberCompatibility
import EtaleCounterexample.RelativeIsoCalculus

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (f : X ⟶ Y) (g : Y ⟶ Z) (s : Spec (.of Ω) ⟶ X)

theorem etaleDirectImageCompIso_point_projection (M : Type u) (U : Z.Etale)
    (l : (Scheme.pointSmallEtale s).fiber.obj ((etaleBaseChange (f ≫ g)).obj U)) :
    (((etaleDirectImageCompIso f g).hom.app ((etalePoint s).directImage.obj M)).hom.app
        (op U)) ≫ Pi.π _ l =
      Pi.π _ ((Scheme.pointSmallEtale s).fiber.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).hom.app U) l) := by
  change Pi.map' (f := fun _ ↦ M) (g := fun _ ↦ M) _ (fun _ ↦ 𝟙 M) ≫ Pi.π _ l = _
  rw [Pi.map'_comp_π, Category.comp_id]
  rfl

/-- Coherence of the actual point-composition and direct-image-composition
comparisons, including an arbitrary equality identifying the output point. -/
theorem etalePointCompIso_composition
    {t : Spec (.of Ω) ⟶ Y} {r : Spec (.of Ω) ⟶ Z}
    (hs : s ≫ f = t) (ht : t ≫ g = r) (M : Type u) :
    (etaleDirectImage g).map ((etalePointCompIsoOfEq f s hs).hom.app M) ≫
        (etalePointCompIsoOfEq g t ht).hom.app M =
      (etaleDirectImageCompIso f g).hom.app ((etalePoint s).directImage.obj M) ≫
        (etalePointCompIsoOfEq (f ≫ g) s
          (show s ≫ (f ≫ g) = r by rw [← Category.assoc, hs, ht])).hom.app M := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext
  intro x
  change (((etalePointCompIsoOfEq f s hs).hom.app M).hom.app
      (op ((etaleBaseChange g).obj U.unop)) ≫
      ((etalePointCompIsoOfEq g t ht).hom.app M).hom.app U) ≫ Pi.π _ x =
    (((etaleDirectImageCompIso f g).hom.app ((etalePoint s).directImage.obj M)).hom.app U ≫
      ((etalePointCompIsoOfEq (f ≫ g) s _).hom.app M).hom.app U) ≫ Pi.π _ x
  rw [Category.assoc, etalePointCompIsoOfEq_projection]
  erw [etalePointCompIsoOfEq_projection]
  rw [Category.assoc, etalePointCompIsoOfEq_projection,
    etaleDirectImageCompIso_point_projection]
  congr 1
  apply CategoryTheory.Over.OverMorphism.ext
  change ((etaleBaseChangeFiberIsoOfEq f s hs).inv.app ((etaleBaseChange g).obj U.unop)
    ((etaleBaseChangeFiberIsoOfEq g t ht).inv.app U.unop x)).left =
    ((etaleBaseChangeFiberIsoOfEq (f ≫ g) s _).inv.app U.unop x).left ≫
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).hom.app U.unop).left
  simp only [etaleBaseChangeFiberIsoOfEq_inv_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullbackComp, hs]
  · simp [MorphismProperty.Over.pullbackComp]

/-- Composition with the actual relative geometric morphism of a scheme map
has exactly the expected relative geometric point, with the structural triangle
proved from the preceding composition coherence. -/
theorem relativeEtalePoint_comp_affineMorphism {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (π : X ⟶ Z) (ρ : Spec R ⟶ Z) (hf : f ≫ ρ = π)
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω) ⟶ Spec R)
    (ω : Spec (.of Ω) ⟶ Z) (hs : s ≫ π = ω) (ht : t ≫ ρ = ω)
    (hst : s ≫ f = t) :
    RelativeCompatible
      ((relativeEtalePoint π s hs).comp (relativeAffineEtaleMorphism f π ρ hf))
      (relativeEtalePoint ρ t ht) (etalePointCompIsoOfEq f s hst) := by
  subst π
  intro M
  simpa [RelativeMorphism.comp, relativeEtalePoint, relativeAffineEtaleMorphism,
    GeometricMorphism.comp] using etalePointCompIso_composition f ρ s hst ht M

end EtaleCounterexample
