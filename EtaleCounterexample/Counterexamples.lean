import EtaleCounterexample.EtaleIdentityCompatibility
import EtaleCounterexample.ArithmeticCounterexample
import EtaleCounterexample.RelativeEndomorphismClass
import EtaleCounterexample.PrimeFieldHomComparison

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The genuine localized endomorphism realization, valued in actual relative
geometric morphisms modulo relative 2-isomorphism. Roof independence, composition,
identity, and agreement with ordinary scheme direct images are proved locally. -/
def localizedEtaleEndomorphismHom :
    End ((relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) →*
      RelativeEndomorphismClass (etaleDirectImage (multiplicativeGroupStructure k)) where
  toFun a := relativeEndomorphismClass (localizedEtaleEndomorphism k p a)
  map_one' := Quotient.sound (localizedEtaleEndomorphism_id k p)
  map_mul' a b := Quotient.sound (localizedEtaleEndomorphism_comp k p b a)

theorem localizedEtaleEndomorphismHom_map
    (f : multiplicativeGroupFiniteType k ⟶ multiplicativeGroupFiniteType k) :
    localizedEtaleEndomorphismHom k p ((relativeUH _).Q.map f) =
      relativeEndomorphismClass
        (relativeMultiplicativeGroupMorphism k (multiplicativeGroupFiniteType k) f) :=
  Quotient.sound (localizedEtaleEndomorphism_map k p f)

variable [Fintype k]

/-- The characteristic is supplied internally for every finite field. -/
def finiteFieldEtaleEndomorphismHom :
    End ((relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) →*
      RelativeEndomorphismClass (etaleDirectImage (multiplicativeGroupStructure k)) := by
  let : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  let : CharP k (ringChar k) := ringChar.charP k
  exact localizedEtaleEndomorphismHom k (ringChar k)

/-- UNCONDITIONAL FINITE-FIELD COUNTEREXAMPLE. The comparison map is the
proved realization of all arrows in the actual finite-type UH localization;
its codomain is the actual relative étale geometric morphisms modulo their
relative compatibility triangles. -/
theorem finiteField_counterexample :
    ∃ T : RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
        (etaleDirectImage (multiplicativeGroupStructure k)),
      IsRelativeEquivalence T ∧ T.geometric.IsPinned.{u} ∧
      ∀ a : End ((relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)),
        relativeEndomorphismClass T ≠ finiteFieldEtaleEndomorphismHom k a := by
  let : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  let : CharP k (ringChar k) := ringChar.charP k
  refine ⟨nonintegralTwist k (multiplicativeGroupStructure k),
    nonintegralTwist_isRelativeEquivalence k _, nonintegralTwist_isPinned k, ?_⟩
  intro a h
  exact nonintegralTwist_not_localizedEtaleEndomorphism k (ringChar k) (AlgebraicClosure k) a
    (Quotient.exact h)

omit [Fact p.Prime] in
/-- The scheme-localization Hom comparison as an equivalence of endomorphism
monoids, hence with arbitrary localized composition respected. -/
def primeFieldEndomorphismEquiv (X : FiniteTypeSchemes (Spec (.of (ZMod p)))) :
    End ((relativeUH _).Q.obj X) ≃*
      End ((relativeUH _).Q.obj ((inclusion (primeBase p)).obj X)) where
  toEquiv := primeFieldFiniteTypeHomEquiv p X X
  map_mul' a b := primeFieldFiniteTypeHomEquiv_comp p b a

/-- Actual arithmetic realization: use the proved localized base-change Hom
equivalence, realize the finite-field arrow, then postcompose its structural
comparison with the actual étale direct image i_*. -/
def arithmeticEtaleEndomorphismHom :
    End ((relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p)) →*
      RelativeEndomorphismClass (arithmeticMultiplicativeGroupStructure p) :=
  (relativeEndomorphismPostcompose (etaleDirectImage (multiplicativeGroupStructure (ZMod p)))
    (etaleDirectImage (primeBase p))).comp
    ((localizedEtaleEndomorphismHom (ZMod p) p).comp
      (primeFieldEndomorphismEquiv p (multiplicativeGroupFiniteType (ZMod p))).symm.toMonoidHom)

theorem arithmetic_chosenRealization_isInduced
    (a : End ((relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p))) :
    IsInducedByArithmeticLocalizedEndomorphism p a
      ((localizedEtaleEndomorphism (ZMod p) p
        ((primeFieldFiniteTypeHomEquiv p _ _).symm a)).postcompose
          (etaleDirectImage (primeBase p))) := by
  let b := (primeFieldFiniteTypeHomEquiv p _ _).symm a
  obtain ⟨r, γ, hγ⟩ := localizedRoof_etaleMorphism_isInduced (ZMod p) p
    (Classical.choice (localizedRoof_nonempty (ZMod p) b))
  have H := (relativeCompatible_postcompose_comp
    (relativeMultiplicativeGroupMorphism (ZMod p) r.source r.denominator)
    (localizedEtaleEndomorphism (ZMod p) p b) (etaleDirectImage (primeBase p))).trans
      (hγ.postcompose (etaleDirectImage (primeBase p)))
  exact ⟨r, _, H⟩

/-- UNCONDITIONAL ARITHMETIC COUNTEREXAMPLE for every prime p. The underlying
scheme is G_m/F_p viewed over Spec Z, and the relative base functor is i_* π_*.
All endomorphisms in the actual arithmetic UH localization are quantified. -/
theorem arithmetic_counterexample :
    ∃ T : RelativeMorphism (arithmeticMultiplicativeGroupStructure p)
        (arithmeticMultiplicativeGroupStructure p),
      IsRelativeEquivalence T ∧ T.geometric.IsPinned.{0} ∧
      ∀ a : End ((relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p)),
        relativeEndomorphismClass T ≠ arithmeticEtaleEndomorphismHom p a := by
  refine ⟨arithmeticNonintegralTwist p, ?_, geometricIdentity_isPinned, ?_⟩
  · exact postcompose_isRelativeEquivalence _ (nonintegralTwist_isRelativeEquivalence (ZMod p) _)
      (etaleDirectImage (primeBase p))
  · intro a h
    have H : RelativelyIsomorphic (arithmeticNonintegralTwist p)
        ((localizedEtaleEndomorphism (ZMod p) p
          ((primeFieldFiniteTypeHomEquiv p _ _).symm a)).postcompose
            (etaleDirectImage (primeBase p))) := Quotient.exact h
    obtain ⟨r, γ, hγ⟩ := arithmetic_chosenRealization_isInduced p a
    apply arithmeticNonintegralTwist_not_induced p a
    exact ⟨r, _, (H.choose_spec.whiskerLeft _).trans hγ⟩

end EtaleCounterexample
