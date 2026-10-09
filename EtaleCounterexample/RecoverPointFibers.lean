import EtaleCounterexample.EtaleMorphisms
import EtaleCounterexample.EtalePoints

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u v w

variable {C : Type v} [Category.{w} C] [LocallySmall.{u} C]
  {J : GrothendieckTopology C} [HasWeakSheafify J (Type u)]

/-- Evaluation of a point on sheafified representables recovers the actual
site fiber, with all sheafification and size comparisons explicit. -/
def sheafifiedYonedaFiberIso (Φ : GrothendieckTopology.Point.{u} J) :
    (shrinkYoneda.{u} ⋙ presheafToSheaf J (Type u)) ⋙ Φ.sheafFiber ≅ Φ.fiber :=
  associator _ _ _ ≪≫
    isoWhiskerLeft _ (Φ.presheafToSheafCompSheafFiberIso (Type u)) ≪≫
    Φ.shrinkYonedaCompPresheafFiberIso

/-- Only the safe implication is used: an isomorphism of sheaf inverse-image
functors induces an isomorphism of the actual site fibers. -/
def recoverSiteFiberIso {Φ Ψ : GrothendieckTopology.Point.{u} J}
    (α : Φ.sheafFiber (A := Type u) ≅ Ψ.sheafFiber) : Φ.fiber ≅ Ψ.fiber :=
  (sheafifiedYonedaFiberIso Φ).symm ≪≫
    isoWhiskerLeft _ α ≪≫ sheafifiedYonedaFiberIso Ψ

/-- An actual isomorphism of étale-point direct images induces a natural
isomorphism on geometric lifts, in the contravariant mate direction. -/
def etalePoint_liftIso_of_rightIso
    {X : AlgebraicGeometry.Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s t : AlgebraicGeometry.Spec (.of Ω) ⟶ X)
    (γ : (etalePoint s).directImage ≅ (etalePoint t).directImage) :
    (AlgebraicGeometry.Scheme.pointSmallEtale t).fiber ≅
      (AlgebraicGeometry.Scheme.pointSmallEtale s).fiber :=
  recoverSiteFiberIso
    ((conjugateIsoEquiv (etalePoint s).adjunction (etalePoint t).adjunction).symm γ)

end EtaleCounterexample
