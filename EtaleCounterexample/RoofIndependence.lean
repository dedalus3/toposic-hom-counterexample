import EtaleCounterexample.LocalizedEtaleEndomorphisms
import EtaleCounterexample.AffineTargetEtale
import EtaleCounterexample.UHCalculus
import EtaleCounterexample.RelativeIsomorphism

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k]

def relativeAffineFiniteTypeMorphism (X Y : FiniteTypeSchemes (Spec (.of k)))
    [IsAffine Y.left] (f : X ⟶ Y) :
    RelativeMorphism (etaleDirectImage X.hom) (etaleDirectImage Y.hom) :=
  relativeAffineTargetEtaleMorphism f.left X.hom Y.hom f.w

theorem relativeAffineFiniteTypeMorphism_comp_Gm
    (P Z : FiniteTypeSchemes (Spec (.of k))) [IsAffine Z.left]
    (r : P ⟶ Z) (s : Z ⟶ multiplicativeGroupFiniteType k) :
    RelativelyIsomorphic
      ((relativeAffineFiniteTypeMorphism k P Z r).comp
        (relativeMultiplicativeGroupMorphism k Z s))
      (relativeMultiplicativeGroupMorphism k P (r ≫ s)) := by
  have : IsAffine (multiplicativeGroupFiniteType k).left :=
    inferInstanceAs (IsAffine (Spec (.of (LaurentPolynomial k))))
  have H₁ := (relativeAffineTargetEtaleMorphism_spec s.left Z.hom
    (multiplicativeGroupStructure k) s.w).symm.whiskerLeft
      (relativeAffineFiniteTypeMorphism k P Z r)
  have H₂ := relativeAffineTargetEtaleMorphism_comp r.left s.left (r ≫ s).left
    P.hom Z.hom (multiplicativeGroupStructure k) r.w s.w rfl (r ≫ s).w
  have H₃ := relativeAffineTargetEtaleMorphism_spec (r ≫ s).left P.hom
    (multiplicativeGroupStructure k) (r ≫ s).w
  exact ⟨_, H₁.trans (H₂.trans H₃)⟩

/-- Equality in the actual localization supplies a common finite-type UH
refinement, not merely equality of the resulting point functions. -/
theorem localizedRoofs_common_refinement
    {a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)}
    (r₁ r₂ : MultiplicativeGroupLocalizedRoof k a) :
    ∃ (P : FiniteTypeSchemes (Spec (.of k))) (t₁ : P ⟶ r₁.source) (t₂ : P ⟶ r₂.source),
      t₁ ≫ r₁.denominator = t₂ ≫ r₂.denominator ∧
      t₁ ≫ r₁.numerator = t₂ ≫ r₂.numerator ∧
      relativeUH _ (t₁ ≫ r₁.denominator) := by
  let W := relativeUH (Spec (.of k))
  let φ : W.RightFraction _ _ := ⟨r₁.denominator, r₁.isUH, r₁.numerator⟩
  let ψ : W.RightFraction _ _ := ⟨r₂.denominator, r₂.isUH, r₂.numerator⟩
  let : IsIso (W.Q.map φ.s) := Localization.inverts W.Q W φ.s φ.hs
  let : IsIso (W.Q.map ψ.s) := Localization.inverts W.Q W ψ.s ψ.hs
  have hφ : φ.map W.Q (Localization.inverts W.Q W) = a := by
    apply (cancel_epi (W.Q.map φ.s)).mp
    rw [φ.map_s_comp_map]
    exact r₁.represents.symm
  have hψ : ψ.map W.Q (Localization.inverts W.Q W) = a := by
    apply (cancel_epi (W.Q.map ψ.s)).mp
    rw [ψ.map_s_comp_map]
    exact r₂.represents.symm
  obtain ⟨P, t₁, t₂, hs, hf, ht⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff W.Q W φ ψ).mp (hφ.trans hψ.symm)
  exact ⟨P, t₁, t₂, hs, hf, ht⟩

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A relative roof triangle remains valid after an actual scheme refinement. -/
theorem relativeRoof_refine
    (Z P : FiniteTypeSchemes (Spec (.of k))) [IsAffine Z.left]
    (s f : Z ⟶ multiplicativeGroupFiniteType k) (r : P ⟶ Z)
    (T : RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
      (etaleDirectImage (multiplicativeGroupStructure k)))
    (h : RelativelyIsomorphic ((relativeMultiplicativeGroupMorphism k Z s).comp T)
      (relativeMultiplicativeGroupMorphism k Z f)) :
    RelativelyIsomorphic ((relativeMultiplicativeGroupMorphism k P (r ≫ s)).comp T)
      (relativeMultiplicativeGroupMorphism k P (r ≫ f)) := by
  let R := relativeAffineFiniteTypeMorphism k P Z r
  let S := relativeMultiplicativeGroupMorphism k Z s
  have H₁ := (relativeAffineFiniteTypeMorphism_comp_Gm k P Z r s).choose_spec.symm.whiskerRight T
  have H₂ := relativeCompatible_associator R S T
  have H₃ := h.choose_spec.whiskerLeft R
  have H₄ := (relativeAffineFiniteTypeMorphism_comp_Gm k P Z r f).choose_spec
  exact ⟨_, H₁.trans (H₂.trans (H₃.trans H₄))⟩

include p in
/-- Any two relative geometric realizations of one actual localized arrow
are relatively isomorphic. The proof uses common scheme refinements and
actual étale composition coherence; it does not use a point-to-topos converse. -/
theorem localizedEtaleRealization_unique
    (a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k))
    (T₁ T₂ : RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
      (etaleDirectImage (multiplicativeGroupStructure k)))
    (h₁ : IsInducedByLocalizedEndomorphism k a T₁)
    (h₂ : IsInducedByLocalizedEndomorphism k a T₂) : RelativelyIsomorphic T₁ T₂ := by
  obtain ⟨r₁, γ₁, hγ₁⟩ := h₁
  obtain ⟨r₂, γ₂, hγ₂⟩ := h₂
  obtain ⟨P, t₁, t₂, hs, hf, ht⟩ := localizedRoofs_common_refinement k r₁ r₂
  have : IsAffine (multiplicativeGroupFiniteType k).left :=
    inferInstanceAs (IsAffine (Spec (.of (LaurentPolynomial k))))
  have : IsAffineHom r₁.denominator.left := isAffineHom_of_homeomorph _
    (universalHomeomorphism_homeomorph _ r₁.isUH)
  have : IsAffine r₁.source.left := isAffine_of_isAffineHom r₁.denominator.left
  have : IsAffineHom r₂.denominator.left := isAffineHom_of_homeomorph _
    (universalHomeomorphism_homeomorph _ r₂.isUH)
  have : IsAffine r₂.source.left := isAffine_of_isAffineHom r₂.denominator.left
  have H₁ := relativeRoof_refine k r₁.source P r₁.denominator r₁.numerator t₁ T₁ ⟨γ₁, hγ₁⟩
  have H₂ := relativeRoof_refine k r₂.source P r₂.denominator r₂.numerator t₂ T₂ ⟨γ₂, hγ₂⟩
  rw [← hs, ← hf] at H₂
  let S := relativeMultiplicativeGroupMorphism k P (t₁ ≫ r₁.denominator)
  let : S.geometric.directImage.IsEquivalence :=
    multiplicativeGroupUH_etaleDirectImage_isEquivalence k p P _ ht
  exact relativelyIsomorphic_cancel_left S T₁ T₂ (H₁.trans H₂.symm)

/-- In particular the chosen localization realization is independent of every
choice of UH roof, up to the required relative 2-isomorphism. -/
theorem localizedEtaleEndomorphism_independent
    {a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)}
    (r : MultiplicativeGroupLocalizedRoof k a) :
    RelativelyIsomorphic (localizedEtaleEndomorphism k p a) (r.etaleMorphism k p) :=
  localizedEtaleRealization_unique k p a _ _
    (localizedRoof_etaleMorphism_isInduced k p (Classical.choice (localizedRoof_nonempty k a)))
    (localizedRoof_etaleMorphism_isInduced k p r)

end EtaleCounterexample
