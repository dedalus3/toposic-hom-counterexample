import EtaleCounterexample.ArithmeticEtaleCoordinates
import EtaleCounterexample.RelativeBaseChange
import EtaleCounterexample.EtalePointComposition

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
namespace EtaleCounterexample
universe u

/-- Replacing composite direct images by their canonical actual scheme
comparisons preserves the relative-point triangle. This uses no faithfulness
assumption about the second direct image. -/
theorem relativeEtalePoint_postcompose_triangle
    {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f : X ⟶ Y) (g : Y ⟶ Z) (s t : Spec (.of Ω) ⟶ X)
    (ω : Spec (.of Ω) ⟶ Y) (hs : s ≫ f = ω) (ht : t ≫ f = ω)
    (γ : (etalePoint s).directImage ≅ (etalePoint t).directImage)
    (hγ : RelativeCompatible
      ((relativeEtalePoint f s hs).postcompose (etaleDirectImage g))
      ((relativeEtalePoint f t ht).postcompose (etaleDirectImage g)) γ) :
    RelativeCompatible
      (relativeEtalePoint (f ≫ g) s (by rw [← Category.assoc, hs]))
      (relativeEtalePoint (f ≫ g) t (by rw [← Category.assoc, ht])) γ := by
  intro M
  apply relativeTriangle_transport (etaleDirectImageCompIso f g)
    ((etaleDirectImage g).map ((etalePointCompIsoOfEq f s hs).hom.app M))
    ((etaleDirectImage g).map ((etalePointCompIsoOfEq f t ht).hom.app M))
    _ _ ((etalePointCompIsoOfEq g ω rfl).hom.app M)
    (etalePointCompIso_composition f g s hs rfl M)
    (etalePointCompIso_composition f g t ht rfl M) (γ.hom.app M)
  simpa only [RelativeMorphism.postcompose, relativeEtalePoint,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] using hγ M

variable (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  [Algebra (ZMod p) Ω] [Algebra.IsAlgebraic (ZMod p) Ω] [CharP Ω p]

/-- Coordinate separation for the arithmetic structural functor i_* π_*.
The conclusion is obtained from actual étale Z-neighborhoods. -/
theorem arithmetic_postcompose_point_eq (z w : Ωˣ)
    (γ : (etalePoint (multiplicativeGroupPoint (ZMod p) Ω z)).directImage ≅
      (etalePoint (multiplicativeGroupPoint (ZMod p) Ω w)).directImage)
    (hγ : RelativeCompatible
      ((relativeEtalePoint (multiplicativeGroupStructure (ZMod p))
        (multiplicativeGroupPoint (ZMod p) Ω z) (multiplicativeGroupPoint_over _ _ _)).postcompose
        (etaleDirectImage (primeBase p)))
      ((relativeEtalePoint (multiplicativeGroupStructure (ZMod p))
        (multiplicativeGroupPoint (ZMod p) Ω w) (multiplicativeGroupPoint_over _ _ _)).postcompose
        (etaleDirectImage (primeBase p))) γ) : z = w := by
  apply arithmetic_relative_multiplicativeGroupPoint_eq p Ω z w γ
  exact relativeEtalePoint_postcompose_triangle _ _ _ _ _ _ _ γ hγ

end EtaleCounterexample
