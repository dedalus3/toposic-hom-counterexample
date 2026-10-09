import EtaleCounterexample.RoofIndependence

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k]

theorem IsInducedByLocalizedEndomorphism.of_relativeIso
    {a : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)}
    {T U : RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
      (etaleDirectImage (multiplicativeGroupStructure k))}
    (hT : IsInducedByLocalizedEndomorphism k a T) (hTU : RelativelyIsomorphic T U) :
    IsInducedByLocalizedEndomorphism k a U := by
  obtain ⟨r, γ, hγ⟩ := hT
  exact ⟨r, _, (hTU.choose_spec.symm.whiskerLeft _).trans hγ⟩

theorem identity_isInducedByLocalizedEndomorphism :
    IsInducedByLocalizedEndomorphism k (𝟙 _)
      (identityTwist (etaleDirectImage (multiplicativeGroupStructure k)) (Iso.refl _)) := by
  let r : MultiplicativeGroupLocalizedRoof k (𝟙 _) := {
    source := multiplicativeGroupFiniteType k
    denominator := 𝟙 _
    numerator := 𝟙 _
    isUH := (relativeUH _).id_mem _
    represents := by simp }
  exact ⟨r, _, relativeCompatible_rightUnitor _⟩

/-- Actual localized composition agrees with composition of the actual
relative geometric realizations. The Ore square is an actual scheme square. -/
theorem IsInducedByLocalizedEndomorphism.comp
    {a b : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)}
    {T U : RelativeMorphism (etaleDirectImage (multiplicativeGroupStructure k))
      (etaleDirectImage (multiplicativeGroupStructure k))}
    (hT : IsInducedByLocalizedEndomorphism k a T)
    (hU : IsInducedByLocalizedEndomorphism k b U) :
    IsInducedByLocalizedEndomorphism k (a ≫ b) (T.comp U) := by
  obtain ⟨r₁, γ₁, hγ₁⟩ := hT
  obtain ⟨r₂, γ₂, hγ₂⟩ := hU
  obtain ⟨P, r, t, hr, hrt⟩ := relativeUH_ore (Spec (.of k))
    r₁.numerator r₂.denominator r₂.isUH
  have hs : relativeUH _ (r ≫ r₁.denominator) :=
    (relativeUH _).comp_mem _ _ hr r₁.isUH
  let rr : MultiplicativeGroupLocalizedRoof k (a ≫ b) := {
    source := P
    denominator := r ≫ r₁.denominator
    numerator := t ≫ r₂.numerator
    isUH := hs
    represents := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc _ a b, r₁.represents, ← Category.assoc, ← Functor.map_comp,
        hrt, Functor.map_comp, Category.assoc, r₂.represents] }
  have : IsAffine (multiplicativeGroupFiniteType k).left :=
    inferInstanceAs (IsAffine (Spec (.of (LaurentPolynomial k))))
  have : IsAffineHom r₁.denominator.left := isAffineHom_of_homeomorph _
    (universalHomeomorphism_homeomorph _ r₁.isUH)
  have : IsAffine r₁.source.left := isAffine_of_isAffineHom r₁.denominator.left
  have : IsAffineHom r₂.denominator.left := isAffineHom_of_homeomorph _
    (universalHomeomorphism_homeomorph _ r₂.isUH)
  have : IsAffine r₂.source.left := isAffine_of_isAffineHom r₂.denominator.left
  have H₁ := relativeRoof_refine k r₁.source P r₁.denominator r₁.numerator r T ⟨γ₁, hγ₁⟩
  have H₂ := relativeRoof_refine k r₂.source P r₂.denominator r₂.numerator t U ⟨γ₂, hγ₂⟩
  rw [hrt] at H₁
  have H := (relativeCompatible_associator
    (relativeMultiplicativeGroupMorphism k P (r ≫ r₁.denominator)) T U).symm.trans
      ((H₁.choose_spec.whiskerRight U).trans H₂.choose_spec)
  exact ⟨rr, _, H⟩

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem localizedEtaleEndomorphism_comp
    (a b : (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k) ⟶
      (relativeUH (Spec (.of k))).Q.obj (multiplicativeGroupFiniteType k)) :
    RelativelyIsomorphic (localizedEtaleEndomorphism k p (a ≫ b))
      ((localizedEtaleEndomorphism k p a).comp (localizedEtaleEndomorphism k p b)) := by
  apply localizedEtaleRealization_unique k p
  · exact localizedRoof_etaleMorphism_isInduced k p _
  · exact (localizedRoof_etaleMorphism_isInduced k p
      (Classical.choice (localizedRoof_nonempty k a))).comp k
        (localizedRoof_etaleMorphism_isInduced k p
          (Classical.choice (localizedRoof_nonempty k b)))

theorem localizedEtaleEndomorphism_id :
    RelativelyIsomorphic (localizedEtaleEndomorphism k p (𝟙 _))
      (identityTwist (etaleDirectImage (multiplicativeGroupStructure k)) (Iso.refl _)) :=
  localizedEtaleRealization_unique k p _ _ _ (localizedRoof_etaleMorphism_isInduced k p _)
    (identity_isInducedByLocalizedEndomorphism k)

end EtaleCounterexample
