import EtaleCounterexample.NonintegralField
import EtaleCounterexample.FiniteEtaleFibers

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Function
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k] [Fintype k]

def finiteEtaleNonintegralAutomorphism (A : CommAlgCat.FiniteEtale.{u} k) : A ≃ₐ[k] A :=
  finiteEtaleFrobenius k A ^ twoPrimaryResidue (orderOf (finiteEtaleFrobenius k A))

theorem finiteEtaleFrobenius_period (A : CommAlgCat.FiniteEtale.{u} k) (x : A) :
    IsPeriodicPt (FiniteField.frobeniusAlgHom k A)
      (orderOf (finiteEtaleFrobenius k A)) x := by
  have h := congrArg (fun e : A ≃ₐ[k] A ↦ e x) (pow_orderOf_eq_one (finiteEtaleFrobenius k A))
  have hF : (finiteEtaleFrobenius k A : A → A) = FiniteField.frobeniusAlgHom k A := by
    funext x
    rfl
  simp only [AlgEquiv.coe_pow, AlgEquiv.one_apply, hF] at h
  exact h

theorem finiteEtaleFrobenius_order_ne_zero (A : CommAlgCat.FiniteEtale.{u} k) :
    orderOf (finiteEtaleFrobenius k A) ≠ 0 := by
  have : Finite A := Module.finite_of_finite k
  have : Finite (A ≃ₐ[k] A) := Finite.of_injective
    (fun e : A ≃ₐ[k] A ↦ (e : A → A)) DFunLike.coe_injective
  exact (orderOf_pos (finiteEtaleFrobenius k A)).ne'

@[simp] theorem finiteEtaleNonintegralAutomorphism_apply
    (A : CommAlgCat.FiniteEtale.{u} k) (x : A) :
    finiteEtaleNonintegralAutomorphism k A x =
      twoPrimaryIterate (FiniteField.frobeniusAlgHom k A) x := by
  rw [twoPrimaryIterate_eq (finiteEtaleFrobenius_order_ne_zero k A)
    (finiteEtaleFrobenius_period k A x)]
  exact congrFun (AlgEquiv.coe_pow (finiteEtaleFrobenius k A) _) x

theorem finiteEtaleNonintegralAutomorphism_natural
    (A B : CommAlgCat.FiniteEtale.{u} k) (a : A →ₐ[k] B) (x : A) :
    a (finiteEtaleNonintegralAutomorphism k A x) =
      finiteEtaleNonintegralAutomorphism k B (a x) := by
  simp only [finiteEtaleNonintegralAutomorphism_apply]
  exact twoPrimaryIterate_natural a (fun x ↦ map_pow a x (Fintype.card k))
    (finiteEtaleFrobenius_order_ne_zero k A) (finiteEtaleFrobenius_period k A x)

/-- The selected nonintegral Frobenius power is natural on the actual finite
étale algebra site, with all components algebra automorphisms. -/
def nonintegralSiteIso :
    𝟭 ((CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) ≅ 𝟭 ((CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :=
  NatIso.ofComponents (fun A ↦ (CommAlgCat.FiniteEtale.isoMk
    (finiteEtaleNonintegralAutomorphism k A.unop)).op) (by
      intro A B f
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      ext x
      exact finiteEtaleNonintegralAutomorphism_natural k B.unop A.unop f.unop.hom.hom x)

/-- An actual natural automorphism of the finite-field étale topos, built from
the selected compatible nonintegral Frobenius powers. -/
def nonintegralToposIso : 𝟭 (EtaleTopos (Spec (.of k))) ≅ 𝟭 (EtaleTopos (Spec (.of k))) :=
  transportIdentityIso (finiteEtaleSheafEquivalence k)
    (siteIdentityAction (finiteEtaleTopology k) (nonintegralSiteIso k))

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

/-- The site automorphism and the single global field automorphism agree on
actual geometric fibers. This is the required connection, not an assumed
Galois/topos equivalence. -/
theorem nonintegralAutomorphism_fiber (A : CommAlgCat.FiniteEtale.{u} k)
    (a : A →ₐ[k] Ω) (x : A) :
    nonintegralFieldAutomorphism k Ω (a x) = a (finiteEtaleNonintegralAutomorphism k A x) := by
  simp only [nonintegralFieldAutomorphism_apply, finiteEtaleNonintegralAutomorphism_apply]
  exact (twoPrimaryIterate_natural a (fun x ↦ map_pow a x (Fintype.card k))
    (finiteEtaleFrobenius_order_ne_zero k A) (finiteEtaleFrobenius_period k A x)).symm

end EtaleCounterexample
