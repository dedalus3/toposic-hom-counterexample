import EtaleCounterexample.SchemeLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u

instance : universalHomeomorphisms.{u}.RespectsIso :=
  inferInstanceAs (topologically IsHomeomorph).universally.RespectsIso

instance : universalHomeomorphisms.{u}.IsStableUnderComposition := by
  let : (topologically IsHomeomorph).IsStableUnderComposition :=
    topologically_isStableUnderComposition _ (fun _ _ hf hg ↦ hg.comp hf)
  exact inferInstanceAs (topologically IsHomeomorph).universally.IsStableUnderComposition

instance : universalHomeomorphisms.{u}.IsMultiplicative where
  id_mem X := by
    intro X' Y' i₁ i₂ f' h
    have : IsIso f' := h.isIso_fst_of_isIso
    exact f'.homeomorph.isHomeomorph

instance (S : Scheme.{u}) : (relativeUH S).IsMultiplicative :=
  inferInstanceAs (universalHomeomorphisms.inverseImage (underlying S)).IsMultiplicative

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem universalHomeomorphism_homeomorph (hf : universalHomeomorphisms f) : IsHomeomorph f :=
  MorphismProperty.universally_le _ f hf

theorem universalHomeomorphism_universallyClosed (hf : universalHomeomorphisms f) :
    UniversallyClosed f := by
  constructor
  intro X' Y' i₁ i₂ f' h
  exact (hf i₁ i₂ f' h).isClosedMap

theorem universalHomeomorphism_universallyInjective (hf : universalHomeomorphisms f) :
    UniversallyInjective f := by
  constructor
  intro X' Y' i₁ i₂ f' h
  exact (hf i₁ i₂ f' h).injective

/-- A scheme morphism which is a homeomorphism is affine. The proof uses affine
basic neighborhoods in the target, and is independent of étale invariance. -/
theorem isAffineHom_of_homeomorph (hf : IsHomeomorph f) : IsAffineHom f := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y)
    (U := ⊤) (by trivial)
  obtain ⟨x, rfl⟩ := hf.surjective y
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := f ⁻¹ᵁ V) hyV
  let W : Y.Opens := ⟨f '' (U : Set X), hf.isOpenMap _ U.isOpen⟩
  obtain ⟨r, hrW, hxr⟩ := hV.exists_basicOpen_le
    (V := W) ⟨f x, ⟨x, hxU, rfl⟩⟩ hyV
  refine ⟨Y.basicOpen r, hxr, hV.basicOpen r, ?_⟩
  have hpre : f ⁻¹ᵁ Y.basicOpen r ≤ U := by
    intro z hz
    obtain ⟨z', hz', he⟩ := hrW hz
    exact hf.injective he ▸ hz'
  have H := hU.basicOpen (X.presheaf.map (homOfLE hUV).op (f.app V r))
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen,
    inf_eq_right.mpr hpre] at H
  exact H

/-- The literal topological definition of UH implies the usual integral and
radicial properties; neither property was assumed in the localization. -/
theorem universalHomeomorphism_integral (hf : universalHomeomorphisms f) : IsIntegralHom f :=
  IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
    ⟨universalHomeomorphism_universallyClosed f hf,
      isAffineHom_of_homeomorph f (universalHomeomorphism_homeomorph f hf)⟩

/-- Injectivity on actual field-valued scheme points. -/
theorem universalHomeomorphism_fieldPoints_injective (hf : universalHomeomorphisms f)
    (K : Type u) [Field K] :
    Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f) := by
  have H : UniversallyInjective f ↔
      ∀ (L : Type u) [Field L], Function.Injective (fun g : Spec (.of L) ⟶ X ↦ g ≫ f) :=
    (tfae_universallyInjective f).out 1 2
  exact H.mp (universalHomeomorphism_universallyInjective f hf) K

/-- Universal homeomorphisms induce bijections on actual algebraically closed
field-valued scheme points. Existence is proved using residue field embeddings. -/
theorem universalHomeomorphism_geometricPoints_bijective
    (hf : universalHomeomorphisms f) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    Function.Bijective (fun g : Spec (.of Ω) ⟶ X ↦ g ≫ f) := by
  refine ⟨universalHomeomorphism_fieldPoints_injective f hf Ω, ?_⟩
  intro s
  obtain ⟨⟨y, a⟩, rfl⟩ := (Y.SpecToEquivOfField Ω).symm.surjective s
  obtain ⟨x, rfl⟩ := (universalHomeomorphism_homeomorph f hf).surjective y
  have H : UniversallyInjective f ↔ Function.Injective f ∧
      ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    (tfae_universallyInjective f).out 1 3
  have hi := (H.mp (universalHomeomorphism_universallyInjective f hf)).2 x
  let m := (f.residueFieldMap x).hom
  dsimp at m
  algebraize [m, a.hom]
  have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hi
  let b : X.residueField x →ₐ[Y.residueField (f x)] Ω := IsAlgClosed.lift
  have hab : f.residueFieldMap x ≫ CommRingCat.ofHom b.toRingHom = a := by
    ext1
    exact b.comp_algebraMap
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x, ?_⟩
  simp [Scheme.SpecToEquivOfField, ← hab]

end EtaleCounterexample
