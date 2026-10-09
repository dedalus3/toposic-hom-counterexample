import EtaleCounterexample.EtalePointComposition
import EtaleCounterexample.EtaleFiberSeparation
import EtaleCounterexample.MultiplicativeGroupPointCoordinates
import EtaleCounterexample.AffineUHInvariance

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k]

/-- The actual relative geometric morphism induced by a morphism to G_m. -/
def relativeMultiplicativeGroupMorphism (Z : FiniteTypeSchemes (Spec (.of k)))
    (f : Z ⟶ multiplicativeGroupFiniteType k) :
    RelativeMorphism (etaleDirectImage Z.hom) (etaleDirectImage (multiplicativeGroupStructure k)) :=
  relativeAffineEtaleMorphism f.left Z.hom (multiplicativeGroupStructure k) f.w

variable [Fintype k] (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (p : ℕ) [Fact p.Prime] [CharP k p] [CharP Ω p]

/-- An arbitrary relative isomorphism after an actual UH roof forces its
scheme-point action to equal the nonintegral twist's action. No converse
from geometric-point agreement to topos isomorphism is used. -/
theorem relative_roof_twist_pointAction
    (Z : FiniteTypeSchemes (Spec (.of k)))
    (s f : Z ⟶ multiplicativeGroupFiniteType k)
    (γ : ((relativeMultiplicativeGroupMorphism k Z s).comp
      (nonintegralTwist k (multiplicativeGroupStructure k))).geometric.directImage ≅
      (relativeMultiplicativeGroupMorphism k Z f).geometric.directImage)
    (hγ : RelativeCompatible
      ((relativeMultiplicativeGroupMorphism k Z s).comp
        (nonintegralTwist k (multiplicativeGroupStructure k)))
      (relativeMultiplicativeGroupMorphism k Z f) γ)
    (z : Ωˣ) (l : Spec (.of Ω) ⟶ Z.left)
    (hl : l ≫ s.left = multiplicativeGroupPoint k Ω z) :
    (Spec.preimage (l ≫ f.left)).hom (LaurentPolynomial.T 1) =
      nonintegralFieldAutomorphism k Ω (z : Ω) := by
  let π := multiplicativeGroupStructure k
  let T := nonintegralTwist k π
  let S := relativeMultiplicativeGroupMorphism k Z s
  let F := relativeMultiplicativeGroupMorphism k Z f
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
  let P := relativeEtalePoint Z.hom l hlbase
  have hS := relativeEtalePoint_comp_affineMorphism s.left Z.hom π s.w
    l (multiplicativeGroupPoint k Ω z) (fieldGeometricPoint k Ω) hlbase
    (multiplicativeGroupPoint_over k Ω z) hl
  have hF := relativeEtalePoint_comp_affineMorphism f.left Z.hom π f.w
    l (multiplicativeGroupPoint k Ω w) (fieldGeometricPoint k Ω) hlbase
    (multiplicativeGroupPoint_over k Ω w) hw
  have hPT := relativeEtalePoint_comp_identityTwist π
    (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)
    (nonintegralToposIso k).symm
  have h₁ := (hS.whiskerRight T).symm
  have h₂ := relativeCompatible_associator P S T
  have h₃ := hγ.whiskerLeft P
  have h₄ := hPT.symm.trans (h₁.trans (h₂.trans (h₃.trans hF)))
  obtain ⟨δ, hδ⟩ := multiplicativeGroup_nonintegral_relativePointAction k Ω z
  have heq := relative_multiplicativeGroupPoint_eq k Ω
    (Units.map (nonintegralFieldAutomorphism k Ω).toMonoidHom z) w _ (hδ.symm.trans h₄)
  have H := congrArg (fun a : Ωˣ ↦ (a : Ω)) heq
  exact H.symm

include Ω p in
/-- The actual nonintegral twist is not induced by ANY finite-type UH roof.
This quantifies over the genuine relative compatibility triangle. -/
theorem nonintegralTwist_no_relative_roof
    (Z : FiniteTypeSchemes (Spec (.of k)))
    (s f : Z ⟶ multiplicativeGroupFiniteType k) (hs : relativeUH _ s) :
    ¬ ∃ γ : ((relativeMultiplicativeGroupMorphism k Z s).comp
        (nonintegralTwist k (multiplicativeGroupStructure k))).geometric.directImage ≅
        (relativeMultiplicativeGroupMorphism k Z f).geometric.directImage,
      RelativeCompatible
        ((relativeMultiplicativeGroupMorphism k Z s).comp
          (nonintegralTwist k (multiplicativeGroupStructure k)))
        (relativeMultiplicativeGroupMorphism k Z f) γ := by
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
  have He := relative_roof_twist_pointAction k Ω Z s f γ hγ (Units.mk0 z hz) l hl
  have Hr := H l (Units.mk0 z hz) hl
  rw [He] at Hr
  exact Hr

end EtaleCounterexample
