import EtaleCounterexample.EtaleFiberSeparation

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Field Ω] [IsSepClosed Ω] [Algebra k Ω]
  {Y : Scheme.{u}} (π : multiplicativeGroup k ⟶ Y) (ω : Spec (.of Ω) ⟶ Y)

def baseEtaleCoordinateLift (U : Y.Etale) (l : (Scheme.pointSmallEtale ω).fiber.obj U)
    (z : Ωˣ) (hz : multiplicativeGroupPoint k Ω z ≫ π = ω) :
    (Scheme.pointSmallEtale (multiplicativeGroupPoint k Ω z)).fiber.obj ((etaleBaseChange π).obj U) :=
  Over.homMk (pullback.lift l.left (multiplicativeGroupPoint k Ω z)
    ((Over.w l).trans hz.symm)) (by simp)

theorem baseEtaleCoordinateLift_eq (U : Y.Etale) (l : (Scheme.pointSmallEtale ω).fiber.obj U)
    (z : Ωˣ) (hz : multiplicativeGroupPoint k Ω z ≫ π = ω) :
    baseEtaleCoordinateLift k Ω π ω U l z hz =
      (etaleBaseChangeFiberIsoOfEq π (multiplicativeGroupPoint k Ω z) hz).inv.app U l := by
  apply Over.OverMorphism.ext
  exact (etaleBaseChangeFiberIsoOfEq_inv_left π _ hz U l).symm

def baseEtaleCoordinateDifference (U : Y.Etale) (r : Γ(U.left, ⊤)) :
    Γ(((etaleBaseChange π).obj U).left, ⊤) :=
  (pullback.fst U.hom π).appTop r -
    (pullback.snd U.hom π).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))

theorem baseEtaleCoordinateDifference_value (U : Y.Etale)
    (l : (Scheme.pointSmallEtale ω).fiber.obj U) (r : Γ(U.left, ⊤))
    (z : Ωˣ) (hz : multiplicativeGroupPoint k Ω z ≫ π = ω) :
    geometricSectionValue (baseEtaleCoordinateLift k Ω π ω U l z hz).left
      (baseEtaleCoordinateDifference k π U r) = geometricSectionValue l.left r - (z : Ω) := by
  let q := baseEtaleCoordinateLift k Ω π ω U l z hz
  have hf : q.left ≫ pullback.fst U.hom π = l.left := pullback.lift_fst ..
  have hs : q.left ≫ pullback.snd U.hom π = multiplicativeGroupPoint k Ω z := Over.w q
  have h₁ : geometricSectionValue q.left ((pullback.fst U.hom π).appTop r) =
      geometricSectionValue l.left r :=
    (geometricSectionValue_comp _ _ _).trans (congrArg (fun t ↦ geometricSectionValue t r) hf)
  have hz' : geometricSectionValue (multiplicativeGroupPoint k Ω z)
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1)) = (z : Ω) :=
    (geometricSectionValue_spec (CommRingCat.ofHom (laurentEvaluation k Ω z).toRingHom) _).trans
      (by change LaurentPolynomial.eval₂ (algebraMap k Ω) z (LaurentPolynomial.T 1) = _; simp)
  have h₂ : geometricSectionValue q.left ((pullback.snd U.hom π).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) = (z : Ω) :=
    (geometricSectionValue_comp _ _ _).trans
      ((congrArg (fun t ↦ geometricSectionValue t
        ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) hs).trans hz')
  exact (geometricSectionValue_sub q.left _ _).trans (congrArg₂ (· - ·) h₁ h₂)

/-- Relative points are separated by ANY actual étale base object carrying the
needed coordinate. This permits arithmetic étale neighborhoods over Spec Z. -/
theorem relativePoint_eq_of_baseEtale_coordinate
    (U : Y.Etale) (l : (Scheme.pointSmallEtale ω).fiber.obj U) (r : Γ(U.left, ⊤))
    (z w : Ωˣ) (hr : geometricSectionValue l.left r = (z : Ω))
    (hz : multiplicativeGroupPoint k Ω z ≫ π = ω)
    (hw : multiplicativeGroupPoint k Ω w ≫ π = ω)
    (γ : (etalePoint (multiplicativeGroupPoint k Ω z)).directImage ≅
      (etalePoint (multiplicativeGroupPoint k Ω w)).directImage)
    (hγ : RelativeCompatible (relativeEtalePoint π _ hz) (relativeEtalePoint π _ hw) γ) :
    z = w := by
  have H := relativePointIso_preserves_baseLifts π _ _ hz hw γ hγ U l
  rw [← baseEtaleCoordinateLift_eq, ← baseEtaleCoordinateLift_eq] at H
  have hz' : geometricSectionValue (baseEtaleCoordinateLift k Ω π ω U l z hz).left
      (baseEtaleCoordinateDifference k π U r) = 0 := by
    rw [baseEtaleCoordinateDifference_value, hr, sub_self]
  have hw' := etaleFiberTransformation_reflects_zero_of_eq (skyscraperFiberTransformation γ.hom)
    _ (baseEtaleCoordinateLift k Ω π ω U l w hw) _ H (baseEtaleCoordinateDifference k π U r) hz'
  rw [baseEtaleCoordinateDifference_value, hr, sub_eq_zero] at hw'
  exact Units.ext hw'

end EtaleCounterexample
