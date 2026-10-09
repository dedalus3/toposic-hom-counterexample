import Mathlib.CategoryTheory.Localization.Construction

set_option autoImplicit false
noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u v
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  [W.IsMultiplicative]

/-- A roof representation, stated without choosing an inverse. -/
def representedByRoof : MorphismProperty W.Localization := fun X Y a ↦
  ∃ (Z : C) (s : Z ⟶ (Localization.Construction.objEquiv W).symm X)
    (f : Z ⟶ (Localization.Construction.objEquiv W).symm Y),
    W s ∧ W.Q.map s ≫ a = W.Q.map f

/-- Only the existence of Ore squares is needed to represent every zigzag;
no cancellation axiom or assertion about equality of roofs is used. -/
theorem every_localized_morphism_has_roof
    (hOre : ∀ {X Y T : C} (f : X ⟶ T) (s : Y ⟶ T), W s →
      ∃ (P : C) (r : P ⟶ X) (t : P ⟶ Y), W r ∧ r ≫ f = t ≫ s)
    (X Y : C) (a : W.Q.obj X ⟶ W.Q.obj Y) :
    ∃ (Z : C) (s : Z ⟶ X) (f : Z ⟶ Y), W s ∧ W.Q.map s ≫ a = W.Q.map f := by
  let : (representedByRoof W).IsStableUnderComposition := ⟨by
    rintro X Y T a b ⟨Z, s, f, hs, hf⟩ ⟨Z', s', f', hs', hf'⟩
    obtain ⟨P, r, t, hr, hrt⟩ := hOre f s' hs'
    refine ⟨P, r ≫ s, t ≫ f', W.comp_mem _ _ hr hs, ?_⟩
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc _ a b, hf, ← Category.assoc, ← Functor.map_comp, hrt,
      Functor.map_comp, Category.assoc, hf']⟩
  have hall : representedByRoof W = ⊤ :=
    Localization.Construction.morphismProperty_eq_top _
      (fun X Y f ↦ ⟨X, 𝟙 X, f, W.id_mem X, by simp⟩)
      (fun X Y s hs ↦ ⟨X, s, 𝟙 X, hs, by
        rw [Functor.map_id]
        exact (Localization.Construction.wIso s hs).hom_inv_id⟩)
  exact (congrFun (congrFun (congrFun hall _) _) a).mpr trivial

end EtaleCounterexample
