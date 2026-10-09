import EtaleCounterexample.RelativePoints

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- Evaluation of the actual Laurent coordinate ring at a nonzero geometric coordinate. -/
def laurentEvaluation (z : Ωˣ) : LaurentPolynomial k →ₐ[k] Ω where
  __ := LaurentPolynomial.eval₂ (algebraMap k Ω) z
  commutes' r := by
    change LaurentPolynomial.eval₂ (algebraMap k Ω) z (algebraMap k _ r) = _
    rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C]

/-- A coordinate gives an actual scheme point of the multiplicative group. -/
def multiplicativeGroupPoint (z : Ωˣ) : Spec (.of Ω) ⟶ multiplicativeGroup k :=
  Spec.map (CommRingCat.ofHom (laurentEvaluation k Ω z).toRingHom)

theorem multiplicativeGroupPoint_over (z : Ωˣ) :
    multiplicativeGroupPoint k Ω z ≫ multiplicativeGroupStructure k =
      fieldGeometricPoint k Ω := by
  change Spec.map (CommRingCat.ofHom (laurentEvaluation k Ω z).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k _)) = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (laurentEvaluation k Ω z).comp_algebraMap

theorem laurentEvaluation_automorphism (σ : Ω ≃ₐ[k] Ω) (z : Ωˣ) :
    σ.toRingHom.comp (laurentEvaluation k Ω z).toRingHom =
      (laurentEvaluation k Ω (Units.map σ.toMonoidHom z)).toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    change σ (LaurentPolynomial.eval₂ (algebraMap k Ω) z (C r)) =
      LaurentPolynomial.eval₂ (algebraMap k Ω) _ (C r)
    simp
  · intro n
    change σ (LaurentPolynomial.eval₂ (algebraMap k Ω) z (T n)) =
      LaurentPolynomial.eval₂ (algebraMap k Ω) _ (T n)
    simp

/-- On coordinates, precomposition by `Spec(σ)` is the positive action `z ↦ σ(z)`. -/
theorem multiplicativeGroupPoint_automorphism (σ : Ω ≃ₐ[k] Ω) (z : Ωˣ) :
    (algebraAutomorphismSpec k Ω σ).hom ≫ multiplicativeGroupPoint k Ω z =
      multiplicativeGroupPoint k Ω (Units.map σ.toMonoidHom z) := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (laurentEvaluation k Ω z).toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (laurentEvaluation_automorphism k Ω σ z)

variable [Fintype k] [Algebra.IsAlgebraic k Ω]

theorem multiplicativeGroupPoint_frobenius (z : Ωˣ) :
    (arithmeticFrobeniusSpec k Ω).hom ≫ multiplicativeGroupPoint k Ω z =
      multiplicativeGroupPoint k Ω (z ^ Fintype.card k) := by
  rw [arithmeticFrobeniusSpec, multiplicativeGroupPoint_automorphism]
  congr 1

/-- The sign calculation specialized to actual points of `G_m`: there is a
relative isomorphism from the inverse-Frobenius twist at `z` to the point at `z^q`. -/
theorem multiplicativeGroup_relativeFrobeniusPointAction [IsSepClosed Ω] (z : Ωˣ) :
    ∃ γ : (etalePoint (multiplicativeGroupPoint k Ω z)).directImage ≅
        (etalePoint (multiplicativeGroupPoint k Ω (z ^ Fintype.card k))).directImage,
      RelativeCompatible
        (twistRelativeEtalePoint (multiplicativeGroupStructure k)
          (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)
          (finiteFieldFrobeniusToposIso k).symm)
        (relativeEtalePoint (multiplicativeGroupStructure k)
          (multiplicativeGroupPoint k Ω (z ^ Fintype.card k))
          (multiplicativeGroupPoint_over k Ω _)) γ := by
  have ht : ((arithmeticFrobeniusSpec k Ω).hom ≫ multiplicativeGroupPoint k Ω z) ≫
      multiplicativeGroupStructure k = fieldGeometricPoint k Ω := by
    rw [Category.assoc, multiplicativeGroupPoint_over, arithmeticFrobeniusSpec_over]
  have H : ∃ γ : (etalePoint (multiplicativeGroupPoint k Ω z)).directImage ≅
        (etalePoint ((arithmeticFrobeniusSpec k Ω).hom ≫
          multiplicativeGroupPoint k Ω z)).directImage,
      RelativeCompatible
        (twistRelativeEtalePoint (multiplicativeGroupStructure k)
          (multiplicativeGroupPoint k Ω z) (multiplicativeGroupPoint_over k Ω z)
          (finiteFieldFrobeniusToposIso k).symm)
        (relativeEtalePoint (multiplicativeGroupStructure k)
          ((arithmeticFrobeniusSpec k Ω).hom ≫ multiplicativeGroupPoint k Ω z) ht) γ :=
    ⟨_, arithmeticFrobenius_relativePointAction k _ _ (multiplicativeGroupPoint_over k Ω z)⟩
  revert H ht
  rw [multiplicativeGroupPoint_frobenius k Ω z]
  intro ht H
  exact H

end EtaleCounterexample
