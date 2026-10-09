import EtaleCounterexample.RelativeIsomorphism
import EtaleCounterexample.RelativeBaseChange

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace EtaleCounterexample
universe u v u₁ v₁ u₂ v₂
variable {E : Type u} [Category.{v} E] {B : Type u₁} [Category.{v₁} B]
  {C : Type u₂} [Category.{v₂} C]

def relativeEndomorphismSetoid (π : E ⥤ B) : Setoid (RelativeMorphism π π) where
  r := RelativelyIsomorphic
  iseqv := ⟨RelativelyIsomorphic.refl, RelativelyIsomorphic.symm, RelativelyIsomorphic.trans⟩

/-- Relative geometric endomorphisms modulo the genuine relative 2-isomorphisms.
The quotient retains the universe of the actual geometric morphism structures. -/
def RelativeEndomorphismClass (π : E ⥤ B) := Quotient (relativeEndomorphismSetoid π)

def relativeEndomorphismClass {π : E ⥤ B} (f : RelativeMorphism π π) :
    RelativeEndomorphismClass π := Quotient.mk _ f

instance (π : E ⥤ B) : Monoid (RelativeEndomorphismClass π) where
  one := relativeEndomorphismClass (identityTwist π (Iso.refl _))
  mul f g := Quotient.liftOn₂ f g (fun f g ↦ relativeEndomorphismClass (g.comp f)) (by
    intro f₁ g₁ f₂ g₂ hf hg
    exact Quotient.sound ⟨_, (hf.choose_spec.whiskerLeft g₁).trans
      (hg.choose_spec.whiskerRight f₂)⟩)
  mul_assoc f g h := Quotient.inductionOn₃ f g h (fun f g h ↦
    Quotient.sound ⟨_, (relativeCompatible_associator h g f).symm⟩)
  one_mul f := Quotient.inductionOn f (fun f ↦
    Quotient.sound ⟨_, relativeCompatible_rightUnitor f⟩)
  mul_one f := Quotient.inductionOn f (fun f ↦
    Quotient.sound ⟨_, relativeCompatible_leftUnitor f⟩)

/-- Postcomposing structural comparisons descends to relative isomorphism
classes. It is not assumed to be injective. -/
def relativeEndomorphismPostcompose (π : E ⥤ B) (J : B ⥤ C) :
    RelativeEndomorphismClass π →* RelativeEndomorphismClass (π ⋙ J) where
  toFun f := Quotient.liftOn f (fun f ↦ relativeEndomorphismClass (f.postcompose J))
    (fun _ _ h ↦ Quotient.sound ⟨_, h.choose_spec.postcompose J⟩)
  map_one' := Quotient.sound ⟨Iso.refl _, by
    intro M
    simp [RelativeMorphism.postcompose, identityTwist, GeometricMorphism.id]
    change 𝟙 _ = J.map (𝟙 _)
    simp⟩
  map_mul' f g := Quotient.inductionOn₂ f g (fun f g ↦
    Quotient.sound ⟨_, (relativeCompatible_postcompose_comp g f J).symm⟩)

end EtaleCounterexample
