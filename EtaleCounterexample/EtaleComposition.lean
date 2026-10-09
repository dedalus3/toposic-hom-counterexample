import EtaleCounterexample.RelativePoints

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u

/-- Actual étale direct images compose, by the canonical iterated-pullback
comparison of the small étale sites. -/
def etaleDirectImageCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleDirectImage f ⋙ etaleDirectImage g ≅ etaleDirectImage (f ≫ g) := by
  letI := etaleBaseChange_continuous f
  letI := etaleBaseChange_continuous g
  letI := etaleBaseChange_continuous (f ≫ g)
  exact Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm
    (Type u) Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- An ordinary scheme morphism to an affine target, over an arbitrary base,
as a genuine relative geometric morphism. Its structural comparison is supplied
by the actual composition isomorphism rather than agreement on points. -/
def relativeAffineEtaleMorphism {X S : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (π : X ⟶ S) (ρ : Spec R ⟶ S) (h : f ≫ ρ = π) :
    RelativeMorphism (etaleDirectImage π) (etaleDirectImage ρ) where
  geometric := affineBaseEtaleMorphism f
  comparison := etaleDirectImageCompIso f ρ ≪≫ eqToIso (congrArg etaleDirectImage h)

end EtaleCounterexample
