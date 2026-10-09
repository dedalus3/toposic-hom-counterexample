import EtaleCounterexample.Relative
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

set_option autoImplicit false

/-!
Actual small étale sheaf categories and their geometric points.
The natural isomorphisms here are constructed, not deduced from agreement on
geometric points. The structural finite-field comparison remains separate.
-/

noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u v w

/-- `Type u`-valued sheaves on the actual small étale site of a `u`-scheme.
The site and sheaf category have object universe `u+1`; fibers are `u`-small. -/
abbrev EtaleTopos (X : Scheme.{u}) := Sheaf X.smallEtaleTopology (Type u)

/-- An actual geometric point as a geometric morphism of sheaf categories. -/
def etalePoint {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) : GeometricMorphism (Type u) (EtaleTopos X) where
  inverseImage := (Scheme.pointSmallEtale s).sheafFiber
  directImage := (Scheme.pointSmallEtale s).skyscraperSheafFunctor
  adjunction := (Scheme.pointSmallEtale s).skyscraperSheafAdjunction
  leftExact := inferInstance

section Reindex
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (e : Spec (.of Ω) ≅ Spec (.of Ω)) (s : Spec (.of Ω) ⟶ X)

/-- Precomposing lifts by `e` gives `U_s ≅ U_(e ≫ s)`, with this direction. -/
def etaleFiberReindex :
    (Scheme.pointSmallEtale s).fiber ≅ (Scheme.pointSmallEtale (e.hom ≫ s)).fiber :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun := fun l ↦ CategoryTheory.Over.homMk (e.hom ≫ l.left) (by
        change (e.hom ≫ l.left) ≫ U.hom = e.hom ≫ s
        have hw : l.left ≫ U.hom = s := CategoryTheory.Over.w l
        rw [Category.assoc, hw])
      invFun := fun l ↦ CategoryTheory.Over.homMk (e.inv ≫ l.left) (by
        change (e.inv ≫ l.left) ≫ U.hom = s
        have hw : l.left ≫ U.hom = e.hom ≫ s := CategoryTheory.Over.w l
        rw [Category.assoc, hw, e.inv_hom_id_assoc])
      left_inv := by intro l; apply CategoryTheory.Over.OverMorphism.ext; simp
      right_inv := by intro l; apply CategoryTheory.Over.OverMorphism.ext; simp }) (by
        intro U V f
        ext l
        apply CategoryTheory.Over.OverMorphism.ext
        simp)

end Reindex

section Extend
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {Φ Ψ : GrothendieckTopology.Point.{u} J}

/-- Extend a transformation of site fibers to presheaf inverse images by the
explicit colimit universal property. -/
def presheafFiberTransformation (α : Φ.fiber ⟶ Ψ.fiber) :
    Φ.presheafFiber (A := Type u) ⟶ Ψ.presheafFiber where
  app P := Φ.presheafFiberDesc
    (fun U x ↦ Ψ.toPresheafFiber U (α.app U x) P) (by
      intro U V f x
      rw [Ψ.toPresheafFiber_w]
      congr 1
      exact (ConcreteCategory.congr_hom (α.naturality f) x).symm)
  naturality {P Q} f := by
    apply Φ.presheafFiber_hom_ext
    intro U x
    simp only [Φ.toPresheafFiber_naturality_assoc,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc_assoc,
      Ψ.toPresheafFiber_naturality]

@[reassoc (attr := simp)]
theorem fiberTransformation_ι (α : Φ.fiber ⟶ Ψ.fiber)
    (P : Cᵒᵖ ⥤ Type u) (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x P ≫ (presheafFiberTransformation α).app P =
      Ψ.toPresheafFiber U (α.app U x) P := by
  simp [presheafFiberTransformation]

/-- Natural isomorphisms of site fibers extend to actual sheaf inverse images. -/
def sheafFiberIso (α : Φ.fiber ≅ Ψ.fiber) :
    Φ.sheafFiber (A := Type u) ≅ Ψ.sheafFiber :=
  isoWhiskerLeft (sheafToPresheaf J (Type u))
    { hom := presheafFiberTransformation α.hom
      inv := presheafFiberTransformation α.inv
      hom_inv_id := by
        apply NatTrans.ext
        funext P
        apply Φ.presheafFiber_hom_ext
        intro U x
        simp
      inv_hom_id := by
        apply NatTrans.ext
        funext P
        apply Ψ.presheafFiber_hom_ext
        intro U x
        simp }

end Extend

/-- The right-adjoint mate on the actual small étale topoi has the reversed
direction: from the point `e ≫ s` to the point `s`. -/
def etalePointRightMate {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (e : Spec (.of Ω) ≅ Spec (.of Ω)) (s : Spec (.of Ω) ⟶ X) :
    (etalePoint (e.hom ≫ s)).directImage ≅ (etalePoint s).directImage :=
  conjugateIsoEquiv (etalePoint (e.hom ≫ s)).adjunction (etalePoint s).adjunction
    (sheafFiberIso (etaleFiberReindex e s))

end EtaleCounterexample
