import EtaleCounterexample.ArithmeticBaseChange
import EtaleCounterexample.RoofNonalgebraicity

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
variable (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  [Algebra (ZMod p) Ω] [Algebra.IsAlgebraic (ZMod p) Ω] [CharP Ω p]
local notation "k" => ZMod p

/-- The relative triangle over Spec Z forces the same explicit nonintegral
point action. Arithmetic point separation is proved by actual étale Z-algebras. -/
theorem arithmetic_relative_roof_twist_pointAction
    (Z : FiniteTypeSchemes (Spec (.of k)))
    (s f : Z ⟶ multiplicativeGroupFiniteType k)
    (γ : (((relativeMultiplicativeGroupMorphism k Z s).postcompose
        (etaleDirectImage (primeBase p))).comp
      ((nonintegralTwist k (multiplicativeGroupStructure k)).postcompose
        (etaleDirectImage (primeBase p)))).geometric.directImage ≅
      ((relativeMultiplicativeGroupMorphism k Z f).postcompose
        (etaleDirectImage (primeBase p))).geometric.directImage)
    (hγ : RelativeCompatible
      (((relativeMultiplicativeGroupMorphism k Z s).postcompose
        (etaleDirectImage (primeBase p))).comp
        ((nonintegralTwist k (multiplicativeGroupStructure k)).postcompose
        (etaleDirectImage (primeBase p))))
      ((relativeMultiplicativeGroupMorphism k Z f).postcompose
        (etaleDirectImage (primeBase p))) γ)
    (z : Ωˣ) (l : Spec (.of Ω) ⟶ Z.left)
    (hl : l ≫ s.left = multiplicativeGroupPoint k Ω z) :
    (Spec.preimage (l ≫ f.left)).hom (LaurentPolynomial.T 1) =
      nonintegralFieldAutomorphism k Ω (z : Ω) := by
  let π := multiplicativeGroupStructure k
  let J := etaleDirectImage (primeBase p)
  let T₀ := nonintegralTwist k π
  let T := T₀.postcompose J
  let S₀ := relativeMultiplicativeGroupMorphism k Z s
  let S := S₀.postcompose J
  let F₀ := relativeMultiplicativeGroupMorphism k Z f
  let F := F₀.postcompose J
  have hsπ : s.left ≫ π = Z.hom := s.w
  have hfπ : f.left ≫ π = Z.hom := f.w
  have hlbase : l ≫ Z.hom = fieldGeometricPoint k Ω := by
    rw [← hsπ, ← Category.assoc, hl]
    exact multiplicativeGroupPoint_over k Ω z
  have hfbase : (l ≫ f.left) ≫ π = fieldGeometricPoint k Ω := by
    rw [Category.assoc, hfπ]
    exact hlbase
  let w := multiplicativeGroupPointUnit k Ω (l ≫ f.left)
  have hw : l ≫ f.left = multiplicativeGroupPoint k Ω w :=
    (multiplicativeGroupPoint_reconstruct k Ω _ hfbase).symm
  let P₀ := relativeEtalePoint Z.hom l hlbase
  let P := P₀.postcompose J
  have hS := relativeEtalePoint_comp_affineMorphism s.left Z.hom π s.w
    l (multiplicativeGroupPoint k Ω z) (fieldGeometricPoint k Ω) hlbase
    (multiplicativeGroupPoint_over k Ω z) hl
  have hF := relativeEtalePoint_comp_affineMorphism f.left Z.hom π f.w
    l (multiplicativeGroupPoint k Ω w) (fieldGeometricPoint k Ω) hlbase
    (multiplicativeGroupPoint_over k Ω w) hw
  have hPT := relativeEtalePoint_comp_identityTwist π
    (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)
    (nonintegralToposIso k).symm
  have hS' := (relativeCompatible_postcompose_comp P₀ S₀ J).trans (hS.postcompose J)
  have hF' := (relativeCompatible_postcompose_comp P₀ F₀ J).trans (hF.postcompose J)
  have hPT' := (relativeCompatible_postcompose_comp
    (relativeEtalePoint π (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z))
    T₀ J).trans (hPT.postcompose J)
  have h₁ := (hS'.whiskerRight T).symm
  have h₂ := relativeCompatible_associator P S T
  have h₃ := hγ.whiskerLeft P
  have h₄ := hPT'.symm.trans (h₁.trans (h₂.trans (h₃.trans hF')))
  obtain ⟨δ, hδ⟩ := multiplicativeGroup_nonintegral_relativePointAction k Ω z
  have heq := arithmetic_postcompose_point_eq p Ω
    (Units.map (nonintegralFieldAutomorphism k Ω).toMonoidHom z) w _ ((hδ.postcompose J).symm.trans h₄)
  have H := congrArg (fun a : Ωˣ ↦ (a : Ω)) heq
  exact H.symm


include Ω in
theorem arithmetic_nonintegralTwist_no_relative_roof
    (Z : FiniteTypeSchemes (Spec (.of k)))
    (s f : Z ⟶ multiplicativeGroupFiniteType k) (hs : relativeUH _ s) :
    ¬ ∃ γ : (((relativeMultiplicativeGroupMorphism k Z s).postcompose
          (etaleDirectImage (primeBase p))).comp
        ((nonintegralTwist k (multiplicativeGroupStructure k)).postcompose
          (etaleDirectImage (primeBase p)))).geometric.directImage ≅
        ((relativeMultiplicativeGroupMorphism k Z f).postcompose
          (etaleDirectImage (primeBase p))).geometric.directImage,
      RelativeCompatible
        (((relativeMultiplicativeGroupMorphism k Z s).postcompose
          (etaleDirectImage (primeBase p))).comp
          ((nonintegralTwist k (multiplicativeGroupStructure k)).postcompose
          (etaleDirectImage (primeBase p))))
        ((relativeMultiplicativeGroupMorphism k Z f).postcompose
          (etaleDirectImage (primeBase p))) γ := by
  rintro ⟨γ, hγ⟩
  have : IsAffine (multiplicativeGroupFiniteType k).left :=
    inferInstanceAs (IsAffine (Spec (.of (LaurentPolynomial k))))
  have : IsAffineHom s.left :=
    isAffineHom_of_homeomorph s.left (universalHomeomorphism_homeomorph s.left hs)
  have : IsAffine Z.left := isAffine_of_isAffineHom s.left
  obtain ⟨d, c, m, _, H⟩ := multiplicativeGroup_roof_monomial k Ω p Z s f hs
  apply nonintegralFieldAutomorphism_no_monomial k Ω p d
  refine ⟨algebraMap k Ω c, m, ?_⟩
  intro z hz
  obtain ⟨l, hl⟩ := (universalHomeomorphism_geometricPoints_bijective s.left hs Ω).surjective
    (multiplicativeGroupPoint k Ω (Units.mk0 z hz))
  have He := arithmetic_relative_roof_twist_pointAction p Ω Z s f γ hγ (Units.mk0 z hz) l hl
  have Hr := H l (Units.mk0 z hz) hl
  rw [He] at Hr
  exact Hr


end EtaleCounterexample
