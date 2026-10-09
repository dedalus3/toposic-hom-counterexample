import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Finite

set_option autoImplicit false

/-!
The genuine relative comparison convention, at the level of geometric morphisms
of categories. The intended instances are étale sheaf categories. No equivalence
with Galois actions is assumed or supplied by this file.
-/

noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable (E : Type u₁) (D : Type u₂) [Category.{v₁} E] [Category.{v₂} D]

/-- A geometric morphism is a finite-limit-preserving left adjoint together with
its right adjoint. On topos categories this is the usual definition. -/
structure GeometricMorphism where
  inverseImage : D ⥤ E
  directImage : E ⥤ D
  adjunction : inverseImage ⊣ directImage
  leftExact : PreservesFiniteLimits inverseImage

def GeometricMorphism.id : GeometricMorphism E E where
  inverseImage := 𝟭 E
  directImage := 𝟭 E
  adjunction := Adjunction.id
  leftExact := inferInstance

variable {E D} {B : Type u₃} [Category.{v₃} B]

/-- `α : ρ_* f_* ≅ π_*`, in Lean's diagrammatic functor-composition order. -/
structure RelativeMorphism (π : E ⥤ B) (ρ : D ⥤ B) where
  geometric : GeometricMorphism E D
  comparison : geometric.directImage ⋙ ρ ≅ π

/-- The comparison triangle is `β ∘ (ρ_* γ) = α`. -/
def RelativeCompatible {π : E ⥤ B} {ρ : D ⥤ B}
    (f h : RelativeMorphism π ρ)
    (γ : f.geometric.directImage ≅ h.geometric.directImage) : Prop :=
  ∀ X, ρ.map (γ.hom.app X) ≫ h.comparison.hom.app X = f.comparison.hom.app X

/-- Identity geometric morphism with its structural comparison twisted by `η`. -/
def identityTwist (π : E ⥤ B) (η : 𝟭 B ≅ 𝟭 B) : RelativeMorphism π π where
  geometric := GeometricMorphism.id E
  comparison := NatIso.ofComponents (fun X ↦ η.app (π.obj X)) (by
    intro X Y f
    simpa [GeometricMorphism.id] using η.hom.naturality (π.map f))

@[simp] theorem identityTwist_directImage (π : E ⥤ B) (η : 𝟭 B ≅ 𝟭 B) :
    (identityTwist π η).geometric.directImage = 𝟭 E := rfl

@[simp] theorem identityTwist_comparison (π : E ⥤ B) (η : 𝟭 B ≅ 𝟭 B) (X : E) :
    (identityTwist π η).comparison.hom.app X = η.hom.app (π.obj X) := rfl

/-- Faithful postcomposition reflects the relative triangle. This is a
conditional categorical lemma; the étale closed-immersion hypothesis is not
proved here. Full faithfulness is stronger than what this implication needs. -/
theorem relativeCompatible_reflected
    {A : Type u₄} [Category.{v₄} A] (J : B ⥤ A) [J.Faithful]
    {π : E ⥤ B} {ρ : D ⥤ B} (f h : RelativeMorphism π ρ)
    (γ : f.geometric.directImage ≅ h.geometric.directImage)
    (hJ : ∀ X, J.map (ρ.map (γ.hom.app X)) ≫ J.map (h.comparison.hom.app X) =
      J.map (f.comparison.hom.app X)) : RelativeCompatible f h γ := by
  intro X
  apply J.map_injective
  simpa only [J.map_comp] using hJ X

/-- Central group elements give natural automorphisms of the action category.
This is about actions in a category; continuity and the étale comparison are
separate obligations. -/
def centralActionIso {V : Type u₁} [Category.{v₁} V]
    {G : Type u₂} [Group G] (g : G) (hg : ∀ h, g * h = h * g) :
    𝟭 (Action V G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents (fun A ↦ Action.mkIso (A.ρAut g) (by
    intro h
    change A.ρ g * A.ρ h = A.ρ h * A.ρ g
    rw [← map_mul, ← map_mul, hg h])) (by
      intro A B f
      ext
      exact (f.comm g).symm)

/-- Transport through a supplied equivalence. This does not assert that any
particular étale/Galois equivalence has been constructed. -/
def transportIdentityIso (e : E ≌ D) (η : 𝟭 E ≅ 𝟭 E) : 𝟭 D ≅ 𝟭 D :=
  e.counitIso.symm ≪≫
    isoWhiskerRight (e.inverse.rightUnitor.symm ≪≫ isoWhiskerLeft e.inverse η ≪≫
      e.inverse.rightUnitor) e.functor ≪≫ e.counitIso

/-- The transported action restricts to the original action under the inverse
equivalence. This records the component convention used for actual base sheaves. -/
theorem transportIdentityIso_inverse_map (e : E ≌ D) (η : 𝟭 E ≅ 𝟭 E) (X : D) :
    e.inverse.map ((transportIdentityIso e η).hom.app X) =
      η.hom.app (e.inverse.obj X) := by
  dsimp [transportIdentityIso]
  simp only [map_comp, Category.id_comp, Category.comp_id]
  rw [← e.unit_app_inverse]
  have h := e.unit.naturality (η.hom.app (e.inverse.obj X))
  dsimp at h
  rw [← Category.assoc, ← h, Category.assoc]
  simp

/-- Inverting a mate square gives exactly the triangle for the inverse base twist. -/
theorem inverseMate_twistTriangle (π : E ⥤ B) {s t : E} {ω : B}
    (γ : t ≅ s) (cs : π.obj s ≅ ω) (ct : π.obj t ≅ ω)
    (η : 𝟭 B ≅ 𝟭 B)
    (h : π.map γ.hom ≫ cs.hom = ct.hom ≫ η.hom.app ω) :
    π.map γ.inv ≫ ct.hom = η.inv.app (π.obj s) ≫ cs.hom := by
  apply (cancel_epi (π.map γ.hom)).mp
  have hn := η.inv.naturality cs.hom
  dsimp only [Functor.id_map] at hn
  simp only [← Category.assoc, ← map_comp, γ.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Category.assoc, ← hn, ← Category.assoc, h, Category.assoc,
    η.hom_inv_id_app]
  exact (Category.comp_id ct.hom).symm

/-- Explicit variance of the right-adjoint mate, with its counit equation. -/
theorem rightMate_counit {Lz Lw : E ⥤ D} {Rz Rw : D ⥤ E}
    (az : Lz ⊣ Rz) (aw : Lw ⊣ Rw) (θ : Lw ≅ Lz) (X : D) :
    Lw.map ((conjugateIsoEquiv az aw θ).hom.app X) ≫ aw.counit.app X =
      θ.hom.app (Rz.obj X) ≫ az.counit.app X :=
  conjugateEquiv_counit az aw θ.hom X

end EtaleCounterexample
