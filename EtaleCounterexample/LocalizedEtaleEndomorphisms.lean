import EtaleCounterexample.RoofNonalgebraicity

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k]

/-- A representative of an arbitrary endomorphism in the ACTUAL finite-type
Gabriel–Zisman localization. Neither affineness nor a Frobenius shape is assumed. -/
structure MultiplicativeGroupLocalizedRoof
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) where
  source : FiniteTypeSchemes (Spec (.of k))
  denominator : source ⟶ multiplicativeGroupFiniteType k
  numerator : source ⟶ multiplicativeGroupFiniteType k
  isUH : relativeUH _ denominator
  represents : (relativeUH _).Q.map denominator ≫ a = (relativeUH _).Q.map numerator

theorem localizedRoof_nonempty
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    Nonempty (MultiplicativeGroupLocalizedRoof k a) := by
  obtain ⟨Z, s, f, hs, ha⟩ := localizedScheme_morphism_has_roof
    (Spec (.of k)) (multiplicativeGroupFiniteType k) (multiplicativeGroupFiniteType k) a
  exact ⟨⟨Z, s, f, hs, ha⟩⟩

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual relative geometric morphism of a UH roof: inverse étale
equivalence of the denominator followed by the numerator. -/
def MultiplicativeGroupLocalizedRoof.etaleMorphism
    {a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)}
    (r : MultiplicativeGroupLocalizedRoof k a) :
    RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
      (etaleDirectImage (multiplicativeGroupStructure k)) := by
  let S := relativeMultiplicativeGroupMorphism k r.source r.denominator
  letI : S.geometric.directImage.IsEquivalence :=
    multiplicativeGroupUH_etaleDirectImage_isEquivalence k p r.source r.denominator r.isUH
  exact S.equivalenceInverse.comp
    (relativeMultiplicativeGroupMorphism k r.source r.numerator)

/-- Every actual localized arrow has at least one such actual relative
geometric realization. The obstruction below quantifies over ALL roofs, so it
does not depend on this choice or assume uniqueness from geometric points. -/
def localizedEtaleEndomorphism
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
      (etaleDirectImage (multiplicativeGroupStructure k)) :=
  (Classical.choice (localizedRoof_nonempty k a)).etaleMorphism k p

/-- Exhaustive algebraization by UH roofs in the actual localization. This
relation asks for the genuine relative triangle after precomposing with the
denominator's actual étale equivalence. -/
def IsInducedByLocalizedEndomorphism
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k))
    (T : RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
      (etaleDirectImage (multiplicativeGroupStructure k))) : Prop :=
  ∃ r : MultiplicativeGroupLocalizedRoof k a,
    ∃ γ : ((relativeMultiplicativeGroupMorphism k r.source r.denominator).comp T).geometric.directImage ≅
        (relativeMultiplicativeGroupMorphism k r.source r.numerator).geometric.directImage,
      RelativeCompatible ((relativeMultiplicativeGroupMorphism k r.source r.denominator).comp T)
        (relativeMultiplicativeGroupMorphism k r.source r.numerator) γ

theorem localizedRoof_etaleMorphism_isInduced
    {a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)}
    (r : MultiplicativeGroupLocalizedRoof k a) :
    IsInducedByLocalizedEndomorphism k a (r.etaleMorphism k p) := by
  let S := relativeMultiplicativeGroupMorphism k r.source r.denominator
  let F := relativeMultiplicativeGroupMorphism k r.source r.numerator
  let : S.geometric.directImage.IsEquivalence :=
    multiplicativeGroupUH_etaleDirectImage_isEquivalence k p r.source r.denominator r.isUH
  exact ⟨r, _, (relativeCompatible_associator S S.equivalenceInverse F).symm.trans
    (((relativeCompatible_comp_inverse S).whiskerRight F).trans
      (relativeCompatible_leftUnitor F))⟩

include p in
theorem localizedEndomorphism_has_etaleRealization
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    ∃ T, IsInducedByLocalizedEndomorphism k a T :=
  ⟨localizedEtaleEndomorphism k p a,
    localizedRoof_etaleMorphism_isInduced k p (Classical.choice (localizedRoof_nonempty k a))⟩

variable [Fintype k] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [CharP Ω p]

include Ω in
/-- No inverse-denominator/numerator realization of ANY localized scheme
endomorphism is relatively isomorphic to the selected nonintegral twist. -/
theorem nonintegralTwist_not_any_localizedRoof
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k))
    (r : MultiplicativeGroupLocalizedRoof k a) :
    ¬ ∃ γ : (nonintegralTwist k (multiplicativeGroupStructure k)).geometric.directImage ≅
        (r.etaleMorphism k p).geometric.directImage,
      RelativeCompatible (nonintegralTwist k (multiplicativeGroupStructure k))
        (r.etaleMorphism k p) γ := by
  rintro ⟨γ, hγ⟩
  let S := relativeMultiplicativeGroupMorphism k r.source r.denominator
  let F := relativeMultiplicativeGroupMorphism k r.source r.numerator
  let T := nonintegralTwist k (multiplicativeGroupStructure k)
  let : S.geometric.directImage.IsEquivalence :=
    multiplicativeGroupUH_etaleDirectImage_isEquivalence k p r.source r.denominator r.isUH
  have h₁ := hγ.whiskerLeft S
  have h₂ := (relativeCompatible_associator S S.equivalenceInverse F).symm
  have h₃ := (relativeCompatible_comp_inverse S).whiskerRight F
  have h₄ := relativeCompatible_leftUnitor F
  exact nonintegralTwist_no_relative_roof k Ω p r.source r.denominator r.numerator r.isUH
    ⟨_, h₁.trans (h₂.trans (h₃.trans h₄))⟩

include Ω in
theorem nonintegralTwist_not_localizedEtaleEndomorphism
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    ¬ ∃ γ : (nonintegralTwist k (multiplicativeGroupStructure k)).geometric.directImage ≅
        (localizedEtaleEndomorphism k p a).geometric.directImage,
      RelativeCompatible (nonintegralTwist k (multiplicativeGroupStructure k))
        (localizedEtaleEndomorphism k p a) γ :=
  nonintegralTwist_not_any_localizedRoof k p Ω a (Classical.choice (localizedRoof_nonempty k a))

include Ω p in
theorem nonintegralTwist_not_induced
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    ¬ IsInducedByLocalizedEndomorphism k a
      (nonintegralTwist k (multiplicativeGroupStructure k)) := by
  rintro ⟨r, γ, hγ⟩
  exact nonintegralTwist_no_relative_roof k Ω p r.source r.denominator r.numerator r.isUH ⟨γ, hγ⟩

end EtaleCounterexample
