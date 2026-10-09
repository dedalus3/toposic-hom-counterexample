import EtaleCounterexample.ArithmeticRoofNonalgebraicity
import EtaleCounterexample.FiniteFieldCounterexample

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
variable (p : ℕ) [Fact p.Prime]

abbrev arithmeticMultiplicativeGroup :=
  (inclusion (primeBase p)).obj (multiplicativeGroupFiniteType (ZMod p))

abbrev arithmeticMultiplicativeGroupStructure :=
  etaleDirectImage (multiplicativeGroupStructure (ZMod p)) ⋙ etaleDirectImage (primeBase p)

/-- The structural functor used below is the direct image of this actual
composite geometric morphism to the small étale topos of Spec Z. -/
def arithmeticMultiplicativeGroupEtaleMorphism :
    GeometricMorphism (EtaleTopos (multiplicativeGroup (ZMod p))) (EtaleTopos (Spec (.of ℤ))) :=
  (multiplicativeGroupEtaleMorphism (ZMod p)).comp (affineBaseEtaleMorphism (primeBase p))

theorem arithmeticMultiplicativeGroupEtaleMorphism_directImage :
    (arithmeticMultiplicativeGroupEtaleMorphism p).directImage =
      arithmeticMultiplicativeGroupStructure p := rfl

/-- The arithmetic twist is exactly i_* applied to the finite-field
structural comparison, with the functor associator made explicit. -/
def arithmeticNonintegralTwist :
    RelativeMorphism (arithmeticMultiplicativeGroupStructure p)
      (arithmeticMultiplicativeGroupStructure p) :=
  (nonintegralTwist (ZMod p) (multiplicativeGroupStructure (ZMod p))).postcompose
    (etaleDirectImage (primeBase p))

/-- Exhaustive arithmetic algebraization relation. The preimage here is the
proved Hom equivalence for the genuine scheme localizations; its proof allows
arbitrary mixed-characteristic intermediate schemes. Each roof is realized by
actual relative étale direct images and the actual denominator equivalence. -/
def IsInducedByArithmeticLocalizedEndomorphism
    (a : (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p) ⟶
      (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p))
    (T : RelativeMorphism (arithmeticMultiplicativeGroupStructure p)
      (arithmeticMultiplicativeGroupStructure p)) : Prop :=
  ∃ r : MultiplicativeGroupLocalizedRoof (ZMod p)
      ((primeFieldFiniteTypeHomEquiv p _ _).symm a),
    ∃ γ : (((relativeMultiplicativeGroupMorphism (ZMod p) r.source r.denominator).postcompose
        (etaleDirectImage (primeBase p))).comp T).geometric.directImage ≅
      ((relativeMultiplicativeGroupMorphism (ZMod p) r.source r.numerator).postcompose
        (etaleDirectImage (primeBase p))).geometric.directImage,
      RelativeCompatible
        (((relativeMultiplicativeGroupMorphism (ZMod p) r.source r.denominator).postcompose
          (etaleDirectImage (primeBase p))).comp T)
        ((relativeMultiplicativeGroupMorphism (ZMod p) r.source r.numerator).postcompose
          (etaleDirectImage (primeBase p))) γ

theorem arithmeticLocalizedEndomorphism_has_etaleRealization
    (a : (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p) ⟶
      (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p)) :
    ∃ T, IsInducedByArithmeticLocalizedEndomorphism p a T := by
  let b := (primeFieldFiniteTypeHomEquiv p _ _).symm a
  obtain ⟨T, r, γ, hγ⟩ := localizedEndomorphism_has_etaleRealization (ZMod p) p b
  have H := (relativeCompatible_postcompose_comp
    (relativeMultiplicativeGroupMorphism (ZMod p) r.source r.denominator) T
    (etaleDirectImage (primeBase p))).trans
    (hγ.postcompose (etaleDirectImage (primeBase p)))
  exact ⟨T.postcompose (etaleDirectImage (primeBase p)), r, _, H⟩

theorem arithmeticNonintegralTwist_not_induced
    (a : (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p) ⟶
      (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p)) :
    ¬ IsInducedByArithmeticLocalizedEndomorphism p a (arithmeticNonintegralTwist p) := by
  rintro ⟨r, γ, hγ⟩
  exact arithmetic_nonintegralTwist_no_relative_roof p (AlgebraicClosure (ZMod p))
    r.source r.denominator r.numerator r.isUH ⟨γ, hγ⟩

/-- The arithmetic counterexample in exhaustive roof form, on the actual
small étale topos and relative to the actual composite i_* π_*. No closed-
subtopos faithfulness hypothesis or point-to-topos converse is assumed. -/
theorem arithmetic_counterexample_roofForm :
    ∃ T : RelativeMorphism (arithmeticMultiplicativeGroupStructure p)
        (arithmeticMultiplicativeGroupStructure p),
      IsRelativeEquivalence T ∧ T.geometric.IsPinned.{0} ∧
      ∀ a : (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p) ⟶
          (relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p),
        ¬ IsInducedByArithmeticLocalizedEndomorphism p a T := by
  refine ⟨arithmeticNonintegralTwist p, ?_, geometricIdentity_isPinned, ?_⟩
  · exact postcompose_isRelativeEquivalence _ (nonintegralTwist_isRelativeEquivalence (ZMod p) _)
      (etaleDirectImage (primeBase p))
  · exact arithmeticNonintegralTwist_not_induced p

end EtaleCounterexample
