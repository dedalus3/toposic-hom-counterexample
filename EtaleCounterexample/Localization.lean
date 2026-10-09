import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

set_option autoImplicit false

/-!
Generic categorical lemma used by the arithmetic localization comparison.
This file alone makes no claim about schemes or étale topoi.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor

namespace EtaleCounterexample

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']

/-- A fully faithful left adjoint remains fully faithful after localizing both
categories, provided both functors descend. This covers all localized morphisms,
not merely roofs of a selected shape. -/
def localizedFullyFaithful
    {I : C ⥤ D} {R : D ⥤ C} (adj : I ⊣ R) [I.Full] [I.Faithful]
    (L : C ⥤ C') (W : MorphismProperty C) [L.IsLocalization W]
    (M : D ⥤ D') (V : MorphismProperty D) [M.IsLocalization V]
    (I' : C' ⥤ D') (R' : D' ⥤ C')
    [CatCommSq I L M I'] [CatCommSq R M L R'] : I'.FullyFaithful := by
  let adj' := adj.localization L W M V I' R'
  haveI hcomp : ∀ X : C, IsIso (adj'.unit.app (L.obj X)) := by
    intro X
    dsimp [adj']
    rw [adj.localization_unit_app]
    infer_instance
  letI := Localization.full_whiskeringLeft L W C'
  letI := Localization.faithful_whiskeringLeft L W C'
  haveI : ∀ X : C, IsIso ((whiskerLeft L adj'.unit).app X) := by
    intro X
    change IsIso (adj'.unit.app (L.obj X))
    exact hcomp X
  haveI : IsIso (whiskerLeft L adj'.unit) :=
    NatIso.isIso_of_isIso_app _
  haveI : IsIso (((Functor.whiskeringLeft C C' C').obj L).map adj'.unit) := by
    change IsIso (whiskerLeft L adj'.unit)
    infer_instance
  haveI : IsIso adj'.unit :=
    isIso_of_reflects_iso adj'.unit ((Functor.whiskeringLeft C C' C').obj L)
  exact adj'.fullyFaithfulLOfIsIsoUnit

end EtaleCounterexample
