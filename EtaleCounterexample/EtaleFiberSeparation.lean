import EtaleCounterexample.RelativeFiberCompatibility
import EtaleCounterexample.MultiplicativeGroupPoints

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u

section OpenDetection
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {s t : Spec (.of Ω) ⟶ X}

/-- A transformation of geometric lift functors preserves membership in opens
of every actual étale object. -/
theorem etaleFiberTransformation_mem_open
    (α : (Scheme.pointSmallEtale t).fiber ⟶ (Scheme.pointSmallEtale s).fiber)
    (U : X.Etale) (l : (Scheme.pointSmallEtale t).fiber.obj U)
    (V : U.left.Opens) (hl : l.left (default : Spec (.of Ω)) ∈ V) :
    (α.app U l).left (default : Spec (.of Ω)) ∈ V := by
  have h : Set.range l.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change l.left x ∈ V
    rw [Subsingleton.elim (α := Spec (.of Ω)) x (default : Spec (.of Ω))]
    exact hl
  let W : X.Etale := MorphismProperty.Over.mk ⊤ (V.ι ≫ U.hom) inferInstance
  let j : W ⟶ U := MorphismProperty.Over.homMk V.ι rfl trivial
  let l' : (Scheme.pointSmallEtale t).fiber.obj W :=
    Over.homMk (IsOpenImmersion.lift V.ι l.left h) (by
      change IsOpenImmersion.lift V.ι l.left h ≫ V.ι ≫ U.hom = t
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w l)
  have he : (Scheme.pointSmallEtale t).fiber.map j l' = l := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac V.ι l.left h
  have hn := ConcreteCategory.congr_hom (α.naturality j) l'
  change α.app U ((Scheme.pointSmallEtale t).fiber.map j l') =
    (Scheme.pointSmallEtale s).fiber.map j (α.app W l') at hn
  rw [he] at hn
  have hh := congrArg (fun q ↦ q.left (default : Spec (.of Ω))) hn
  change (α.app U l).left (default : Spec (.of Ω)) = V.ι ((α.app W l').left (default : Spec (.of Ω))) at hh
  rw [hh]
  exact ((α.app W l').left (default : Spec (.of Ω))).property

/-- Evaluate a global section at the actual scheme geometric point. -/
def geometricSectionValue {Y : Scheme.{u}} (l : Spec (.of Ω) ⟶ Y)
    (r : Γ(Y, ⊤)) : Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom (l.appTop r)

omit [IsSepClosed Ω] in
@[simp] theorem geometricSectionValue_sub {Y : Scheme.{u}}
    (l : Spec (.of Ω) ⟶ Y) (r r' : Γ(Y, ⊤)) :
    geometricSectionValue l (r - r') =
      geometricSectionValue l r - geometricSectionValue l r' := by
  simp [geometricSectionValue]

omit [IsSepClosed Ω] in
theorem geometricSectionValue_comp {Y Z : Scheme.{u}}
    (l : Spec (.of Ω) ⟶ Y) (f : Y ⟶ Z) (r : Γ(Z, ⊤)) :
    geometricSectionValue l (f.appTop r) = geometricSectionValue (l ≫ f) r := by
  simp [geometricSectionValue]

omit [IsSepClosed Ω] in
@[simp] theorem geometricSectionValue_spec {R : CommRingCat.{u}}
    (a : R ⟶ CommRingCat.of Ω) (r : R) :
    geometricSectionValue (Spec.map a) ((Scheme.ΓSpecIso R).inv r) = a r := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality a) r
  dsimp [CommRingCat.comp_apply] at h
  dsimp [geometricSectionValue]
  rw [← h]
  simp

omit [IsSepClosed Ω] in
theorem geometricSectionValue_ne_zero_iff {Y : Scheme.{u}}
    (l : Spec (.of Ω) ⟶ Y) (r : Γ(Y, ⊤)) :
    geometricSectionValue l r ≠ 0 ↔ l (default : Spec (.of Ω)) ∈ Y.basicOpen r := by
  have he : l.appTop r = (Scheme.ΓSpecIso (.of Ω)).inv (geometricSectionValue l r) := by
    simp [geometricSectionValue]
  constructor
  · intro h
    have hu : IsUnit (l.appTop r) := by
      rw [he]
      exact (isUnit_iff_ne_zero.mpr h).map (Scheme.ΓSpecIso (.of Ω)).inv.hom
    have hp : l ⁻¹ᵁ Y.basicOpen r = ⊤ := by
      rw [Scheme.Hom.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
    exact congrArg (fun V : (Spec (.of Ω)).Opens ↦ (default : Spec (.of Ω)) ∈ V) hp |>.mpr trivial
  · intro h hn
    have hz : l.appTop r = 0 := by rw [he, hn, map_zero]
    have hp : l ⁻¹ᵁ Y.basicOpen r = ⊥ := by
      rw [Scheme.Hom.preimage_basicOpen_top, hz, Scheme.basicOpen_zero]
    have hh : (default : Spec (.of Ω)) ∈ l ⁻¹ᵁ Y.basicOpen r := h
    rw [hp] at hh
    exact hh

/-- Vanishing at the image lift forces vanishing at the original lift. -/
theorem etaleFiberTransformation_reflects_zero
    (α : (Scheme.pointSmallEtale t).fiber ⟶ (Scheme.pointSmallEtale s).fiber)
    (U : X.Etale) (l : (Scheme.pointSmallEtale t).fiber.obj U)
    (r : Γ(U.left, ⊤))
    (h : geometricSectionValue (α.app U l).left r = 0) :
    geometricSectionValue l.left r = 0 := by
  by_contra hn
  have hi := etaleFiberTransformation_mem_open α U l (U.left.basicOpen r)
    ((geometricSectionValue_ne_zero_iff l.left r).mp hn)
  exact ((geometricSectionValue_ne_zero_iff _ r).mpr hi) h

/-- The same vanishing implication with a specified image lift. -/
theorem etaleFiberTransformation_reflects_zero_of_eq
    (α : (Scheme.pointSmallEtale t).fiber ⟶ (Scheme.pointSmallEtale s).fiber)
    (U : X.Etale) (l : (Scheme.pointSmallEtale t).fiber.obj U)
    (l' : (Scheme.pointSmallEtale s).fiber.obj U) (he : α.app U l = l')
    (r : Γ(U.left, ⊤)) (h : geometricSectionValue l'.left r = 0) :
    geometricSectionValue l.left r = 0 := by
  subst l'
  exact etaleFiberTransformation_reflects_zero α U l r h

end OpenDetection

section Coordinates
variable (k Ω : Type u) [Field k] [Field Ω] [IsSepClosed Ω] [Algebra k Ω]

/-- The function `a - t` on the base change by a finite étale algebra. -/
def coordinateDifference (A : CommAlgCat.FiniteEtale.{u} k) (a : A) :
    Γ(((etaleBaseChange (multiplicativeGroupStructure k)).obj
      (finiteEtaleScheme k (op A))).left, ⊤) :=
  (pullback.fst (finiteEtaleScheme k (op A)).hom (multiplicativeGroupStructure k)).appTop
      ((Scheme.ΓSpecIso (.of A)).inv a) -
    (pullback.snd (finiteEtaleScheme k (op A)).hom (multiplicativeGroupStructure k)).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (T 1))

/-- The chosen geometric lift to the actual finite étale base change. -/
def finiteEtaleBaseLift (A : CommAlgCat.FiniteEtale.{u} k) (b : A →ₐ[k] Ω) (z : Ωˣ) :
    (Scheme.pointSmallEtale (multiplicativeGroupPoint k Ω z)).fiber.obj
      ((etaleBaseChange (multiplicativeGroupStructure k)).obj (finiteEtaleScheme k (op A))) :=
  Over.homMk (pullback.lift ((finiteEtaleLiftEquiv k Ω A).symm b).left
    (multiplicativeGroupPoint k Ω z)
    ((Over.w ((finiteEtaleLiftEquiv k Ω A).symm b)).trans
      (multiplicativeGroupPoint_over k Ω z).symm)) (by simp)

/-- The explicit pullback lift agrees with the structural point comparison. -/
theorem finiteEtaleBaseLift_eq (A : CommAlgCat.FiniteEtale.{u} k)
    (b : A →ₐ[k] Ω) (z : Ωˣ) :
    finiteEtaleBaseLift k Ω A b z =
      (etaleBaseChangeFiberIsoOfEq (multiplicativeGroupStructure k)
        (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)).inv.app
        (finiteEtaleScheme k (op A)) ((finiteEtaleLiftEquiv k Ω A).symm b) := by
  apply Over.OverMorphism.ext
  exact (etaleBaseChangeFiberIsoOfEq_inv_left (multiplicativeGroupStructure k)
    (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)
    (finiteEtaleScheme k (op A)) ((finiteEtaleLiftEquiv k Ω A).symm b)).symm

/-- Evaluation on the actual pullback point has the expected two coordinates. -/
theorem coordinateDifference_value (A : CommAlgCat.FiniteEtale.{u} k)
    (b : A →ₐ[k] Ω) (a : A) (z : Ωˣ) :
    geometricSectionValue (finiteEtaleBaseLift k Ω A b z).left
      (coordinateDifference k A a) = b a - (z : Ω) := by
  let l := (finiteEtaleLiftEquiv k Ω A).symm b
  let q := finiteEtaleBaseLift k Ω A b z
  have hf : q.left ≫ pullback.fst (finiteEtaleScheme k (op A)).hom
      (multiplicativeGroupStructure k) = l.left :=
    pullback.lift_fst _ _ _
  have hs : q.left ≫ pullback.snd (finiteEtaleScheme k (op A)).hom
      (multiplicativeGroupStructure k) = multiplicativeGroupPoint k Ω z := Over.w q
  have h₁ : geometricSectionValue q.left
      ((pullback.fst (finiteEtaleScheme k (op A)).hom
        (multiplicativeGroupStructure k)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)) = b a :=
    (geometricSectionValue_comp _ _ _).trans
      ((congrArg (fun v ↦ geometricSectionValue v ((Scheme.ΓSpecIso (.of A)).inv a)) hf).trans
        (geometricSectionValue_spec (CommRingCat.ofHom b.toRingHom) a))
  have hz : geometricSectionValue (multiplicativeGroupPoint k Ω z)
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (T 1)) = (z : Ω) :=
    (geometricSectionValue_spec
      (CommRingCat.ofHom (laurentEvaluation k Ω z).toRingHom) (T 1)).trans
        (by change LaurentPolynomial.eval₂ (algebraMap k Ω) z (T 1) = _; simp)
  have h₂ : geometricSectionValue q.left
      ((pullback.snd (finiteEtaleScheme k (op A)).hom
        (multiplicativeGroupStructure k)).appTop
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (T 1))) = (z : Ω) :=
    (geometricSectionValue_comp _ _ _).trans
      ((congrArg (fun v ↦ geometricSectionValue v
        ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (T 1))) hs).trans hz)
  exact (geometricSectionValue_sub q.left _ _).trans (congrArg₂ (· - ·) h₁ h₂)

/-- A base-preserving map on lifts detects the coordinate after a finite étale
base change. Its hypothesis is supplied by the actual relative triangle below. -/
theorem point_eq_of_finiteEtale_liftMap
    (A : CommAlgCat.FiniteEtale.{u} k) (b : A →ₐ[k] Ω) (a : A)
    (z w : Ωˣ) (ha : b a = (z : Ω))
    (α : (Scheme.pointSmallEtale (multiplicativeGroupPoint k Ω w)).fiber ⟶
      (Scheme.pointSmallEtale (multiplicativeGroupPoint k Ω z)).fiber)
    (hbase : α.app ((etaleBaseChange (multiplicativeGroupStructure k)).obj
        (finiteEtaleScheme k (op A))) (finiteEtaleBaseLift k Ω A b w) =
      finiteEtaleBaseLift k Ω A b z) :
    z = w := by
  let q := finiteEtaleBaseLift k Ω A b
  have hz : geometricSectionValue (q z).left (coordinateDifference k A a) = 0 :=
    (coordinateDifference_value k Ω A b a z).trans
      ((congrArg (fun v ↦ v - (z : Ω)) ha).trans (sub_self _))
  have hw := etaleFiberTransformation_reflects_zero_of_eq α _ (q w) (q z)
    hbase (coordinateDifference k A a) hz
  have hw' : b a - (w : Ω) = 0 := (coordinateDifference_value k Ω A b a w).symm.trans hw
  exact Units.ext (ha.symm.trans (sub_eq_zero.mp hw'))

/-- Finite étale coordinates separate relative geometric points. This helper
keeps the finite-extension witness explicit; the theorem below supplies it. -/
theorem relativePoint_eq_of_finiteEtale_coordinate
    (A : CommAlgCat.FiniteEtale.{u} k) (b : A →ₐ[k] Ω) (a : A)
    (z w : Ωˣ) (ha : b a = (z : Ω))
    (γ : (etalePoint (multiplicativeGroupPoint k Ω z)).directImage ≅
      (etalePoint (multiplicativeGroupPoint k Ω w)).directImage)
    (hγ : RelativeCompatible
      (relativeEtalePoint (multiplicativeGroupStructure k)
        (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z))
      (relativeEtalePoint (multiplicativeGroupStructure k)
        (multiplicativeGroupPoint k Ω w) (multiplicativeGroupPoint_over k Ω w)) γ) :
    z = w := by
  apply point_eq_of_finiteEtale_liftMap k Ω A b a z w ha (skyscraperFiberTransformation γ.hom)
  rw [finiteEtaleBaseLift_eq, finiteEtaleBaseLift_eq]
  exact relativePointIso_preserves_baseLifts _ _ _ _ _ γ hγ _ _

variable [Fintype k] [Algebra.IsAlgebraic k Ω]

omit [IsSepClosed Ω] in
/-- Every algebraic coordinate over a finite field lies in an actual finite
étale algebra. No étale/Galois equivalence is postulated. -/
theorem exists_finiteEtale_coordinate (z : Ω) :
    ∃ (A : CommAlgCat.FiniteEtale.{u} k) (b : A →ₐ[k] Ω) (a : A), b a = z := by
  let L := IntermediateField.adjoin k {z}
  have : FiniteDimensional k L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  have : Algebra.Etale k L :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  refine ⟨CommAlgCat.FiniteEtale.of k L, IntermediateField.val L, ⟨z, ?_⟩, rfl⟩
  exact IntermediateField.subset_adjoin k {z} (Set.mem_singleton z)

/-- An arbitrary relative isomorphism of actual geometric points of `G_m/k`
forces their coordinates to agree. Only this direction is asserted. -/
theorem relative_multiplicativeGroupPoint_eq (z w : Ωˣ)
    (γ : (etalePoint (multiplicativeGroupPoint k Ω z)).directImage ≅
      (etalePoint (multiplicativeGroupPoint k Ω w)).directImage)
    (hγ : RelativeCompatible
      (relativeEtalePoint (multiplicativeGroupStructure k)
        (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z))
      (relativeEtalePoint (multiplicativeGroupStructure k)
        (multiplicativeGroupPoint k Ω w) (multiplicativeGroupPoint_over k Ω w)) γ) :
    z = w := by
  obtain ⟨A, b, a, ha⟩ := exists_finiteEtale_coordinate k Ω (z : Ω)
  exact relativePoint_eq_of_finiteEtale_coordinate k Ω A b a z w ha γ hγ

end Coordinates
end EtaleCounterexample
