import EtaleCounterexample.UniversalHomeomorphisms
import Mathlib.CategoryTheory.Types.Basic

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (ω : Spec (.of Ω) ⟶ S)

/-- Actual relative field-valued scheme points; the algebraic closure need not
be a finite-type object. -/
def schemePoints (X : FiniteTypeSchemes S) :=
  {x : Spec (.of Ω) ⟶ X.left // x ≫ X.hom = ω}

def schemePointsFunctor : FiniteTypeSchemes S ⥤ Type u where
  obj X := schemePoints ω X
  map {X Y} f := ↾fun x ↦ ⟨x.val ≫ f.left, by
    rw [Category.assoc, show f.left ≫ Y.hom = X.hom from by simp]
    exact x.property⟩
  map_id X := by ext x; apply Subtype.ext; exact Category.comp_id _
  map_comp f g := by ext x; apply Subtype.ext; exact (Category.assoc _ _ _).symm

variable [IsAlgClosed Ω]

theorem schemePointsFunctor_invertsUH : (relativeUH S).IsInvertedBy (schemePointsFunctor ω) := by
  intro X Y f hf
  apply (isIso_iff_bijective _).mpr
  obtain ⟨hi, hs⟩ := universalHomeomorphism_geometricPoints_bijective f.left hf Ω
  constructor
  · intro x y h
    apply Subtype.ext
    exact hi (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := hs y.val
    change x ≫ f.left = y.val at hx
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    rw [← show f.left ≫ Y.hom = X.hom from by simp, ← Category.assoc, hx]
    exact y.property

/-- The genuine point functor on the Gabriel–Zisman scheme localization. -/
def localizedSchemePoints : LocalizedSchemes S ⥤ Type u :=
  Localization.Construction.lift (schemePointsFunctor ω) (schemePointsFunctor_invertsUH ω)

theorem localizedSchemePoints_comp_Q :
    (relativeUH S).Q ⋙ localizedSchemePoints ω = schemePointsFunctor ω :=
  Localization.Construction.fac _ _

/-- The localized point action agrees with the original action on every scheme
morphism, and therefore on arbitrary zigzags by the localization construction. -/
theorem localizedSchemePoints_map (X Y : FiniteTypeSchemes S) (f : X ⟶ Y) :
    (localizedSchemePoints ω).map ((relativeUH S).Q.map f) =
      (schemePointsFunctor ω).map f := by
  exact Functor.congr_hom (localizedSchemePoints_comp_Q ω) f

end EtaleCounterexample
