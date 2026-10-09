import EtaleCounterexample.RelativeIsoCalculus

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
variable {A : Type u₁} {E : Type u₂} {D : Type u₃} {B : Type u₄}
  [Category.{v₁} A] [Category.{v₂} E] [Category.{v₃} D] [Category.{v₄} B]
  {σ : A ⥤ B} {π : E ⥤ B} {ρ : D ⥤ B}

def RelativelyIsomorphic (f g : RelativeMorphism π ρ) : Prop :=
  ∃ γ : f.geometric.directImage ≅ g.geometric.directImage, RelativeCompatible f g γ

theorem RelativelyIsomorphic.refl (f : RelativeMorphism π ρ) : RelativelyIsomorphic f f :=
  ⟨_, RelativeCompatible.refl f⟩

theorem RelativelyIsomorphic.symm {f g : RelativeMorphism π ρ}
    (h : RelativelyIsomorphic f g) : RelativelyIsomorphic g f :=
  ⟨_, h.choose_spec.symm⟩

theorem RelativelyIsomorphic.trans {f g h : RelativeMorphism π ρ}
    (hfg : RelativelyIsomorphic f g) (hgh : RelativelyIsomorphic g h) :
    RelativelyIsomorphic f h := ⟨_, hfg.choose_spec.trans hgh.choose_spec⟩

theorem RelativelyIsomorphic.whiskerLeft (a : RelativeMorphism σ π)
    {f g : RelativeMorphism π ρ} (h : RelativelyIsomorphic f g) :
    RelativelyIsomorphic (a.comp f) (a.comp g) := ⟨_, h.choose_spec.whiskerLeft a⟩

/-- Cancellation of a genuine relative equivalence on the source side. -/
theorem relativelyIsomorphic_cancel_left (a : RelativeMorphism σ π)
    [a.geometric.directImage.IsEquivalence] (f g : RelativeMorphism π ρ)
    (h : RelativelyIsomorphic (a.comp f) (a.comp g)) : RelativelyIsomorphic f g := by
  have hf : RelativelyIsomorphic (a.equivalenceInverse.comp (a.comp f)) f :=
    ⟨_, (relativeCompatible_associator a.equivalenceInverse a f).symm.trans
      (((relativeCompatible_inverse_comp a).whiskerRight f).trans
        (relativeCompatible_leftUnitor f))⟩
  have hg : RelativelyIsomorphic (a.equivalenceInverse.comp (a.comp g)) g :=
    ⟨_, (relativeCompatible_associator a.equivalenceInverse a g).symm.trans
      (((relativeCompatible_inverse_comp a).whiskerRight g).trans
        (relativeCompatible_leftUnitor g))⟩
  exact hf.symm.trans ((h.whiskerLeft a.equivalenceInverse).trans hg)

end EtaleCounterexample
