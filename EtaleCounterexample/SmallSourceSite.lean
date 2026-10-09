import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u v w

section
variable {C : Type u} [SmallCategory C] {D : Type v} [Category.{u} D]
  (F : C ⥤ D)

/-- The pointwise left Kan extension formula with a small source and a locally
small, possibly large target. No universe enlargement of the values is needed. -/
def smallSourceLanEvaluation (X : D) :
    F.lan ⋙ (evaluation D (Type u)).obj X ≅
      (whiskeringLeft _ _ (Type u)).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ Type u) => IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

instance smallSourceLan_preservesFiniteLimits [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShape_of_natIso (smallSourceLanEvaluation F.op K).symm

end
end EtaleCounterexample
