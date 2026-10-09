import EtaleCounterexample.RelativePoints
import Mathlib.CategoryTheory.Limits.Types.Products

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u v w

section Fibers
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {Φ Ψ : GrothendieckTopology.Point.{u} J}

/-- The universal tuple of elements of a site fiber, in its categorical product. -/
def fiberUniversalTuple (I : Type u) : ∏ᶜ (fun _ : I ↦ I) :=
  (Types.productIso (fun _ : I ↦ I)).inv id

@[simp] theorem fiberUniversalTuple_projection (I : Type u) (i : I) :
    Pi.π (fun _ : I ↦ I) i (fiberUniversalTuple I) = i := by
  exact ConcreteCategory.congr_hom (Types.productIso_inv_comp_π (fun _ : I ↦ I) i) id

/-- Recover the map of lift sets directly from a transformation of the actual
skyscraper direct images. This is the covariant Yoneda calculation on sets. -/
def skyscraperFiberMap
    (α : Φ.skyscraperSheafFunctor (A := Type u) ⟶ Ψ.skyscraperSheafFunctor)
    (U : C) (x : Ψ.fiber.obj U) : Φ.fiber.obj U :=
  Pi.π (fun _ : Ψ.fiber.obj U ↦ Φ.fiber.obj U) x ((α.app (Φ.fiber.obj U)).hom.app (op U)
    (fiberUniversalTuple (Φ.fiber.obj U)))

/-- Every component is precomposition with the recovered map, derived using
naturality in the target set; no classification of topos points is assumed. -/
@[reassoc]
theorem skyscraperFiberMap_projection
    (α : Φ.skyscraperSheafFunctor (A := Type u) ⟶ Ψ.skyscraperSheafFunctor)
    (M : Type u) (U : C) (x : Ψ.fiber.obj U) :
    (α.app M).hom.app (op U) ≫ Pi.π _ x =
      Pi.π _ (skyscraperFiberMap α U x) := by
  apply ConcreteCategory.hom_ext
  intro t
  let f : Φ.fiber.obj U ⟶ M := ↾fun i ↦ Pi.π (fun _ : Φ.fiber.obj U ↦ M) i t
  have hn := congrArg (fun q ↦ q.hom.app (op U)) (α.naturality f)
  have he : (Φ.skyscraperSheafFunctor.map f).hom.app (op U)
      (fiberUniversalTuple (Φ.fiber.obj U)) = t := by
    apply (Types.productIso (fun _ : Φ.fiber.obj U ↦ M)).toEquiv.injective
    funext i
    change Pi.π (fun _ : Φ.fiber.obj U ↦ M) i ((CategoryTheory.Limits.Pi.map (fun _ : Φ.fiber.obj U ↦ f)) (fiberUniversalTuple (Φ.fiber.obj U))) = Pi.π (fun _ : Φ.fiber.obj U ↦ M) i t
    rw [Types.pi_map_π_apply]
    simp [f]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q ≫ Pi.π _ x) hn) (fiberUniversalTuple (Φ.fiber.obj U))
  change Pi.π (fun _ : Ψ.fiber.obj U ↦ M) x
    ((α.app M).hom.app (op U)
      ((Φ.skyscraperSheafFunctor.map f).hom.app (op U)
        (fiberUniversalTuple (Φ.fiber.obj U)))) =
    Pi.π (fun _ : Ψ.fiber.obj U ↦ M) x
      ((CategoryTheory.Limits.Pi.map (fun _ : Ψ.fiber.obj U ↦ f))
        ((α.app (Φ.fiber.obj U)).hom.app (op U)
          (fiberUniversalTuple (Φ.fiber.obj U)))) at h
  rw [he] at h
  rw [Types.pi_map_π_apply] at h
  simpa [skyscraperFiberMap, f] using h

theorem skyscraperFiberMap_naturality
    (α : Φ.skyscraperSheafFunctor (A := Type u) ⟶ Ψ.skyscraperSheafFunctor)
    {U V : C} (f : U ⟶ V) (x : Ψ.fiber.obj U) :
    skyscraperFiberMap α V (Ψ.fiber.map f x) =
      Φ.fiber.map f (skyscraperFiberMap α U x) := by
  have h := congrArg (fun q ↦ q ≫ Pi.π _ x)
    ((α.app (Φ.fiber.obj V)).hom.naturality f.op)
  change (Pi.map' (fun x ↦ Φ.fiber.map f x) (fun _ : Φ.fiber.obj U ↦ 𝟙 (Φ.fiber.obj V)) ≫
    (α.app (Φ.fiber.obj V)).hom.app (op U)) ≫ Pi.π _ x =
    ((α.app (Φ.fiber.obj V)).hom.app (op V) ≫
    Pi.map' (fun x ↦ Ψ.fiber.map f x) (fun _ : Ψ.fiber.obj U ↦ 𝟙 (Φ.fiber.obj V))) ≫ Pi.π _ x at h
  simp only [Category.assoc, Pi.map'_comp_π, Category.comp_id] at h
  erw [skyscraperFiberMap_projection, skyscraperFiberMap_projection] at h
  simp only [Pi.map'_comp_π, Category.comp_id] at h
  have h' := ConcreteCategory.congr_hom h (fiberUniversalTuple (Φ.fiber.obj V))
  simpa using h'.symm

/-- Contravariant recovery of a natural transformation of the actual site fibers. -/
def skyscraperFiberTransformation
    (α : Φ.skyscraperSheafFunctor (A := Type u) ⟶ Ψ.skyscraperSheafFunctor) :
    Ψ.fiber ⟶ Φ.fiber where
  app U := ↾skyscraperFiberMap α U
  naturality {U V} f := by
    ext x
    exact skyscraperFiberMap_naturality α f x

end Fibers

section Relative
variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The structural lift comparison with an explicitly fixed base point. -/
def etaleBaseChangeFiberIsoOfEq (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    {ω : Spec (.of Ω) ⟶ Y} (h : s ≫ f = ω) :
    etaleBaseChange f ⋙ (Scheme.pointSmallEtale s).fiber ≅
      (Scheme.pointSmallEtale ω).fiber :=
  etaleBaseChangeFiberIso f s ≪≫
    eqToIso (congrArg (fun ω ↦ (Scheme.pointSmallEtale ω).fiber) h)

@[reassoc]
theorem etaleBaseChangeFiberIsoOfEq_inv_fst (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    {ω : Spec (.of Ω) ⟶ Y} (h : s ≫ f = ω) (U : Y.Etale)
    (x : (Scheme.pointSmallEtale ω).fiber.obj U) :
    ((etaleBaseChangeFiberIsoOfEq f s h).inv.app U x).left ≫
        pullback.fst U.hom f = x.left := by
  subst ω
  simp [etaleBaseChangeFiberIsoOfEq, etaleBaseChangeFiberIso]

/-- An explicit formula avoids transporting the lift itself through an
equality of structural points. -/
theorem etaleBaseChangeFiberIsoOfEq_inv_left (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    {ω : Spec (.of Ω) ⟶ Y} (h : s ≫ f = ω) (U : Y.Etale)
    (x : (Scheme.pointSmallEtale ω).fiber.obj U) :
    ((etaleBaseChangeFiberIsoOfEq f s h).inv.app U x).left =
      pullback.lift x.left s ((Over.w x).trans h.symm) := by
  subst ω
  simp [etaleBaseChangeFiberIsoOfEq, etaleBaseChangeFiberIso]

@[reassoc]
theorem etalePointCompIsoOfEq_projection (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    {ω : Spec (.of Ω) ⟶ Y} (h : s ≫ f = ω) (M : Type u) (U : Y.Etale)
    (x : (Scheme.pointSmallEtale ω).fiber.obj U) :
    ((etalePointCompIsoOfEq f s h).hom.app M).hom.app (op U) ≫ Pi.π _ x =
      Pi.π _ ((etaleBaseChangeFiberIsoOfEq f s h).inv.app U x) := by
  subst ω
  simpa [etalePointCompIsoOfEq, etaleBaseChangeFiberIsoOfEq] using
    etalePointCompIso_projection f s M U x

/-- The genuine relative triangle forces the recovered map on geometric lifts
to preserve every lift from the base, with both structural comparisons included.
This holds for an arbitrary relative isomorphism, not only constructed mates. -/
theorem relativePointIso_preserves_baseLifts (f : X ⟶ Y)
    (s t : Spec (.of Ω) ⟶ X) {ω : Spec (.of Ω) ⟶ Y}
    (hs : s ≫ f = ω) (ht : t ≫ f = ω)
    (γ : (etalePoint s).directImage ≅ (etalePoint t).directImage)
    (hγ : RelativeCompatible (relativeEtalePoint f s hs) (relativeEtalePoint f t ht) γ)
    (U : Y.Etale) (x : (Scheme.pointSmallEtale ω).fiber.obj U) :
    skyscraperFiberMap γ.hom ((etaleBaseChange f).obj U)
        ((etaleBaseChangeFiberIsoOfEq f t ht).inv.app U x) =
      (etaleBaseChangeFiberIsoOfEq f s hs).inv.app U x := by
  let M := (Scheme.pointSmallEtale s).fiber.obj ((etaleBaseChange f).obj U)
  have h := congrArg (fun q ↦ q.hom.app (op U) ≫ Pi.π (fun _ ↦ M) x) (hγ M)
  change (((γ.hom.app M).hom.app (op ((etaleBaseChange f).obj U))) ≫
    ((etalePointCompIsoOfEq f t ht).hom.app M).hom.app (op U)) ≫ Pi.π _ x =
      ((etalePointCompIsoOfEq f s hs).hom.app M).hom.app (op U) ≫ Pi.π _ x at h
  rw [Category.assoc, etalePointCompIsoOfEq_projection,
    etalePointCompIsoOfEq_projection] at h
  erw [skyscraperFiberMap_projection (Φ := Scheme.pointSmallEtale s)
    (Ψ := Scheme.pointSmallEtale t)] at h
  simpa [M] using ConcreteCategory.congr_hom h (fiberUniversalTuple M)

end Relative
end EtaleCounterexample
