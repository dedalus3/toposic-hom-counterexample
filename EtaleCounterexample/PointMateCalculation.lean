import EtaleCounterexample.EtaleMorphisms

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u v w

section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (Φ Ψ : GrothendieckTopology.Point.{u} J)

@[reassoc (attr := simp)]
theorem toFiber_counit (M : Type u) (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x (Φ.skyscraperSheaf M).obj ≫
      Φ.skyscraperSheafAdjunction.counit.app M = Pi.π _ x := by
  have h : Φ.skyscraperSheafAdjunction.counit.app M =
      (Φ.skyscraperSheafAdjunction.homEquiv _ _).symm (𝟙 (Φ.skyscraperSheaf M)) := by
    simp [Adjunction.homEquiv_symm_apply]
  rw [h]
  erw [Φ.skyscraperSheafAdjunction_homEquiv_symm_apply]
  simp

/-- The mate acts by precomposition on the product indexed by geometric lifts.
This derives the formula from the actual sheaf adjunction. -/
@[reassoc]
theorem pointMate_projection (α : Φ.fiber ≅ Ψ.fiber) (M : Type u) (U : C)
    (x : Φ.fiber.obj U) :
    ((conjugateIsoEquiv Ψ.skyscraperSheafAdjunction Φ.skyscraperSheafAdjunction
      (sheafFiberIso α)).hom.app M).hom.app (op U) ≫ Pi.π _ x =
      Pi.π _ (α.hom.app U x) := by
  let β := (conjugateIsoEquiv Ψ.skyscraperSheafAdjunction Φ.skyscraperSheafAdjunction
    (sheafFiberIso α)).hom
  have h : β.app M = (Φ.skyscraperSheafAdjunction.homEquiv _ _)
      ((sheafFiberIso α).hom.app (Ψ.skyscraperSheaf M) ≫
        Ψ.skyscraperSheafAdjunction.counit.app M) := by
    apply (Φ.skyscraperSheafAdjunction.homEquiv _ _).symm.injective
    dsimp only [Functor.id_obj]
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply]
    exact conjugateEquiv_counit Ψ.skyscraperSheafAdjunction
      Φ.skyscraperSheafAdjunction (sheafFiberIso α).hom M
  change (β.app M).hom.app (op U) ≫ _ = _
  rw [h]
  erw [Φ.skyscraperSheafAdjunction_homEquiv_apply_hom,
    Φ.skyscraperPresheafHomEquiv_app_π]
  change Φ.toPresheafFiber U x (Ψ.skyscraperSheaf M).obj ≫
      (presheafFiberTransformation α.hom).app _ ≫ _ = _
  rw [fiberTransformation_ι_assoc, toFiber_counit]

end

section Comparison
variable {C : Type v} [Category.{w} C] {D : Type*} [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  (Φ : GrothendieckTopology.Point.{u} K) (Ψ : GrothendieckTopology.Point.{u} J)

/-- A comparison of site fibers gives an explicit comparison of the direct
images of the associated geometric points. -/
def skyscraperBaseComparison (α : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    Φ.skyscraperSheafFunctor ⋙ F.sheafPushforwardContinuous (Type u) J K ≅
      Ψ.skyscraperSheafFunctor :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ <|
    NatIso.ofComponents (fun U : Cᵒᵖ ↦ (piFunctor.obj M).mapIso (α.app U.unop).symm.op)
      (by
        intro U V f
        dsimp
        apply Pi.hom_ext
        intro x
        simp only [Category.assoc, Pi.map'_comp_π, Category.comp_id]
        congr 1
        exact (ConcreteCategory.congr_hom (α.inv.naturality f.unop) x).symm)) (by
    intro M N g
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply Pi.hom_ext
    intro x
    simp [piFunctor])

@[reassoc (attr := simp)]
theorem skyscraperBaseComparison_projection (α : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (M : Type u) (U : C) (x : Ψ.fiber.obj U) :
    ((skyscraperBaseComparison F Φ Ψ α).hom.app M).hom.app (op U) ≫ Pi.π _ x =
      Pi.π _ (α.inv.app U x) := by
  simp [skyscraperBaseComparison, piFunctor]

end Comparison

section SchemeComparison
variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)

/-- The pullback universal property identifies the two geometric lift sets. -/
def etaleBaseChangeFiberIso :
    etaleBaseChange f ⋙ (Scheme.pointSmallEtale s).fiber ≅
      (Scheme.pointSmallEtale (s ≫ f)).fiber :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun := fun l ↦ CategoryTheory.Over.homMk (l.left ≫ pullback.fst U.hom f) (by
        have hl : l.left ≫ pullback.snd U.hom f = s := CategoryTheory.Over.w l
        change (l.left ≫ pullback.fst U.hom f) ≫ U.hom = s ≫ f
        rw [Category.assoc, pullback.condition, ← Category.assoc, hl])
      invFun := fun l ↦ CategoryTheory.Over.homMk
        (pullback.lift l.left s (CategoryTheory.Over.w l)) (by simp)
      left_inv := by
        intro l
        apply CategoryTheory.Over.OverMorphism.ext
        apply pullback.hom_ext
        · simp
        · simpa using (CategoryTheory.Over.w l).symm
      right_inv := by
        intro l
        apply CategoryTheory.Over.OverMorphism.ext
        simp }) (by
    intro U V g
    ext l
    apply CategoryTheory.Over.OverMorphism.ext
    change (l.left ≫ pullback.lift (pullback.fst U.hom f ≫ g.left)
      (pullback.snd U.hom f) _) ≫ pullback.fst V.hom f =
      (l.left ≫ pullback.fst U.hom f) ≫ g.left
    simp [Category.assoc])

/-- Structural comparison for actual geometric points and actual étale direct image. -/
def etalePointCompIso :
    (etalePoint s).directImage ⋙ etaleDirectImage f ≅ (etalePoint (s ≫ f)).directImage :=
  skyscraperBaseComparison (etaleBaseChange f) (Scheme.pointSmallEtale s)
    (Scheme.pointSmallEtale (s ≫ f)) (etaleBaseChangeFiberIso f s)

@[reassoc]
theorem etalePointCompIso_projection (M : Type u) (U : Y.Etale)
    (x : (Scheme.pointSmallEtale (s ≫ f)).fiber.obj U) :
    ((etalePointCompIso f s).hom.app M).hom.app (op U) ≫ Pi.π _ x =
      Pi.π _ ((etaleBaseChangeFiberIso f s).inv.app U x) :=
  skyscraperBaseComparison_projection (etaleBaseChange f) (Scheme.pointSmallEtale s)
    (Scheme.pointSmallEtale (s ≫ f)) (etaleBaseChangeFiberIso f s) M U x

end SchemeComparison

section ReindexEquation
variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (e : Spec (.of Ω) ≅ Spec (.of Ω))

/-- Reindex lifts with an explicit equality of the resulting scheme points. -/
def etaleFiberReindexOfEq {s t : Spec (.of Ω) ⟶ X} (h : e.hom ≫ s = t) :
    (Scheme.pointSmallEtale s).fiber ≅ (Scheme.pointSmallEtale t).fiber :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun := fun l ↦ CategoryTheory.Over.homMk (e.hom ≫ l.left) (by
        change (e.hom ≫ l.left) ≫ U.hom = t
        have hl : l.left ≫ U.hom = s := CategoryTheory.Over.w l
        rw [Category.assoc, hl, h])
      invFun := fun l ↦ CategoryTheory.Over.homMk (e.inv ≫ l.left) (by
        change (e.inv ≫ l.left) ≫ U.hom = s
        have hl : l.left ≫ U.hom = t := CategoryTheory.Over.w l
        rw [Category.assoc, hl, ← h, e.inv_hom_id_assoc])
      left_inv := by intro l; apply CategoryTheory.Over.OverMorphism.ext; simp
      right_inv := by intro l; apply CategoryTheory.Over.OverMorphism.ext; simp }) (by
    intro U V g
    ext l
    apply CategoryTheory.Over.OverMorphism.ext
    simp)

def etalePointRightMateOfEq {s t : Spec (.of Ω) ⟶ X} (h : e.hom ≫ s = t) :
    (etalePoint t).directImage ≅ (etalePoint s).directImage :=
  conjugateIsoEquiv (etalePoint t).adjunction (etalePoint s).adjunction
    (sheafFiberIso (etaleFiberReindexOfEq e h))

@[reassoc]
theorem etalePointRightMateOfEq_projection {s t : Spec (.of Ω) ⟶ X}
    (h : e.hom ≫ s = t) (M : Type u) (U : X.Etale)
    (x : (Scheme.pointSmallEtale s).fiber.obj U) :
    ((etalePointRightMateOfEq e h).hom.app M).hom.app (op U) ≫ Pi.π _ x =
      Pi.π _ ((etaleFiberReindexOfEq e h).hom.app U x) :=
  pointMate_projection (Scheme.pointSmallEtale s) (Scheme.pointSmallEtale t)
    (etaleFiberReindexOfEq e h) M U x

set_option maxHeartbeats 400000 in
/-- Base naturality of the actual right-adjoint mate, with structural
comparison isomorphisms included explicitly. -/
theorem etalePointRightMate_base (f : X ⟶ Y) {s t : Spec (.of Ω) ⟶ X}
    (h : e.hom ≫ s = t) (M : Type u) :
    (etaleDirectImage f).map ((etalePointRightMateOfEq e h).hom.app M) ≫
        (etalePointCompIso f s).hom.app M =
      (etalePointCompIso f t).hom.app M ≫
        (etalePointRightMateOfEq e (show e.hom ≫ (s ≫ f) = t ≫ f by
          rw [← Category.assoc, h])).hom.app M := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext
  intro x
  change (((etaleDirectImage f).map ((etalePointRightMateOfEq e h).hom.app M)).hom.app U ≫
    ((etalePointCompIso f s).hom.app M).hom.app U) ≫ Pi.π _ x =
    (((etalePointCompIso f t).hom.app M).hom.app U ≫
      ((etalePointRightMateOfEq e (show e.hom ≫ (s ≫ f) = t ≫ f by
        rw [← Category.assoc, h])).hom.app M).hom.app U) ≫ Pi.π _ x
  simp only [Category.assoc]
  rw [etalePointCompIso_projection f s M U.unop x]
  erw [etalePointRightMateOfEq_projection e h M ((etaleBaseChange f).obj U.unop)
    ((etaleBaseChangeFiberIso f s).inv.app U.unop x)]
  rw [etalePointRightMateOfEq_projection e _ M U.unop x]
  rw [etalePointCompIso_projection f t M U.unop]
  congr 1
  apply CategoryTheory.Over.OverMorphism.ext
  change e.hom ≫ pullback.lift x.left s _ = pullback.lift (e.hom ≫ x.left) t _
  apply pullback.hom_ext <;> simp [h]

end ReindexEquation
end EtaleCounterexample
