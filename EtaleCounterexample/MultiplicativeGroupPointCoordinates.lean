import EtaleCounterexample.LocalizedMonomial

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

def multiplicativeGroupPointUnit
    (s : Spec (.of Ω) ⟶ multiplicativeGroup k) : Ωˣ :=
  Units.map (Spec.preimage s).hom.toMonoidHom (isUnit_T (R := k) 1).unit

omit [Algebra k Ω] in
@[simp] theorem multiplicativeGroupPointUnit_val
    (s : Spec (.of Ω) ⟶ multiplicativeGroup k) :
    (multiplicativeGroupPointUnit k Ω s : Ω) = (Spec.preimage s).hom (T 1) := by
  simp [multiplicativeGroupPointUnit]

/-- Every actual relative scheme point of G_m has a unique nonzero Laurent
coordinate. The reconstruction is proved on ring maps, not on topos points. -/
theorem multiplicativeGroupPoint_reconstruct
    (s : Spec (.of Ω) ⟶ multiplicativeGroup k)
    (hs : s ≫ multiplicativeGroupStructure k = fieldGeometricPoint k Ω) :
    multiplicativeGroupPoint k Ω (multiplicativeGroupPointUnit k Ω s) = s := by
  have hc : ∀ c : k, (Spec.preimage s).hom (C c) = algebraMap k Ω c := by
    have H := congrArg Spec.preimage hs
    rw [Spec.preimage_comp] at H
    rw [multiplicativeGroupStructure, fieldGeometricPoint, Spec.preimage_map,
      Spec.preimage_map] at H
    change CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)) ≫ Spec.preimage s =
      CommRingCat.ofHom (algebraMap k Ω) at H
    intro c
    exact congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of Ω ↦ φ.hom c) H
  have H : (laurentEvaluation k Ω (multiplicativeGroupPointUnit k Ω s)).toRingHom =
      (Spec.preimage s).hom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
    apply Polynomial.ringHom_ext
    · intro c
      change LaurentPolynomial.eval₂ (algebraMap k Ω) _
        (algebraMap (Polynomial k) (LaurentPolynomial k) (Polynomial.C c)) = _
      simpa [algebraMap_eq_toLaurent] using (hc c).symm
    · change LaurentPolynomial.eval₂ (algebraMap k Ω) _
        (algebraMap (Polynomial k) (LaurentPolynomial k) Polynomial.X) = _
      simp [algebraMap_eq_toLaurent]
  change Spec.map (CommRingCat.ofHom _) = s
  rw [H]
  exact Spec.map_preimage s

end EtaleCounterexample
