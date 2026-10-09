import EtaleCounterexample.SchemeRoofs
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u

theorem surjective_closedImmersion_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f] :
    universalHomeomorphisms f := by
  intro X' Y' i₁ i₂ f' h
  have : IsClosedImmersion f' := MorphismProperty.of_isPullback h.flip inferInstance
  have : Surjective f' := MorphismProperty.of_isPullback h.flip inferInstance
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(IsClosedImmersion.isClosedEmbedding f').isEmbedding, Surjective.surj (f := f')⟩

theorem universalHomeomorphism_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : universalHomeomorphisms f) : universalHomeomorphisms (pullback.diagonal f) := by
  have : IsIntegralHom f := universalHomeomorphism_integral f hf
  have : UniversallyInjective f := universalHomeomorphism_universallyInjective f hf
  have : Surjective (pullback.diagonal f) := (UniversallyInjective.iff_diagonal f).mp inferInstance
  exact surjective_closedImmersion_universalHomeomorphism _

instance : universalHomeomorphisms.{u}.HasOfPostcompProperty universalHomeomorphisms :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    (fun _ _ f hf ↦ universalHomeomorphism_diagonal f hf)

variable (S : Scheme.{u}) [IsNoetherian S]

theorem relativeUH_equalizer {X Y Y' : FiniteTypeSchemes S}
    (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (hs : relativeUH S s)
    (h : f₁ ≫ s = f₂ ≫ s) :
    ∃ (X' : FiniteTypeSchemes S) (t : X' ⟶ X), relativeUH S t ∧ t ≫ f₁ = t ≫ f₂ := by
  have h' : f₁.left ≫ s.left = f₂.left ≫ s.left :=
    congrArg (fun a ↦ a.left) h
  let b := pullback.lift f₁.left f₂.left h'
  have : IsIntegralHom s.left := universalHomeomorphism_integral s.left hs
  let t := pullback.fst b (pullback.diagonal s.left)
  have htft : finiteType t := ⟨inferInstance, inferInstance⟩
  let X' : FiniteTypeSchemes S := MorphismProperty.Over.mk ⊤ (t ≫ X.hom)
    (finiteType.comp_mem _ _ htft X.prop)
  refine ⟨X', MorphismProperty.Over.homMk t rfl trivial,
    universalHomeomorphisms.pullback_fst b _ (universalHomeomorphism_diagonal s.left hs), ?_⟩
  apply MorphismProperty.Over.Hom.ext
  change t ≫ f₁.left = t ≫ f₂.left
  have H := pullback.condition (f := b) (g := pullback.diagonal s.left)
  have H₁ := congrArg (fun a ↦ a ≫ pullback.fst s.left s.left) H
  have H₂ := congrArg (fun a ↦ a ≫ pullback.snd s.left s.left) H
  simp only [b, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at H₁ H₂
  exact H₁.trans H₂.symm

instance : (relativeUH S).HasRightCalculusOfFractions where
  exists_rightFraction {X Y} φ := by
    obtain ⟨P, r, t, hr, hrt⟩ := relativeUH_ore S φ.f φ.s φ.hs
    exact ⟨⟨r, hr, t⟩, hrt⟩
  ext {X Y Y'} f₁ f₂ s hs h := by
    obtain ⟨X', t, ht, htf⟩ := relativeUH_equalizer S f₁ f₂ s hs h
    exact ⟨X', t, ht, htf⟩

end EtaleCounterexample
