import EtaleCounterexample.FiniteEtaleComparison
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u v w

/-- A natural automorphism of a site acts on sheaves by restriction along its
forward components. -/
def siteIdentityAction {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    (τ : 𝟭 C ≅ 𝟭 C) : 𝟭 (Sheaf J (Type u)) ≅ 𝟭 (Sheaf J (Type u)) :=
  (Functor.sheafPushforwardContinuousId (Type u) J).symm ≪≫
    Functor.sheafPushforwardContinuousIso τ.symm (Type u) J J ≪≫
    Functor.sheafPushforwardContinuousId (Type u) J

@[simp]
theorem siteIdentityAction_component {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (τ : 𝟭 C ≅ 𝟭 C) (P : Sheaf J (Type u)) (U : C) :
    ((siteIdentityAction J τ).hom.app P).hom.app (op U) =
      P.obj.map (τ.hom.app U).op := by
  simp [siteIdentityAction, Functor.sheafPushforwardContinuousId,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]

variable (k : Type u) [Field k] [Fintype k]

/-- Frobenius is an automorphism on every finite étale algebra over a finite
field, including the zero algebra. -/
def finiteEtaleFrobenius (A : CommAlgCat.FiniteEtale.{u} k) : A ≃ₐ[k] A :=
  AlgEquiv.ofBijective (FiniteField.frobeniusAlgHom k A) (by
    nontriviality A
    obtain ⟨p, hp, e, he, hcard⟩ := FiniteField.card' k
    have : Fact p.Prime := ⟨he⟩
    have : CharP A p := charP_of_injective_algebraMap' k p
    have : Finite A := Module.finite_of_finite k
    have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
    exact (FiniteField.frobeniusAlgEquiv k A p).bijective)

@[simp] theorem finiteEtaleFrobenius_apply (A : CommAlgCat.FiniteEtale.{u} k) (x : A) :
    finiteEtaleFrobenius k A x = x ^ Fintype.card k := rfl

/-- The scheme-direction Frobenius natural automorphism on the finite étale site. -/
def finiteEtaleFrobeniusSiteIso :
    𝟭 ((CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) ≅ 𝟭 ((CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :=
  NatIso.ofComponents (fun A ↦ (CommAlgCat.FiniteEtale.isoMk
    (finiteEtaleFrobenius k A.unop)).op) (by
      intro A B f
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      ext x
      exact map_pow f.unop.hom.hom x (Fintype.card k))

/-- An actual natural automorphism of the identity on the finite-field étale
topos, transported through the proved finite-étale sheaf comparison. Its full
Galois interpretation is a separate theorem still to establish. -/
def finiteFieldFrobeniusToposIso :
    𝟭 (EtaleTopos (Spec (.of k))) ≅ 𝟭 (EtaleTopos (Spec (.of k))) :=
  transportIdentityIso (finiteEtaleSheafEquivalence k)
    (siteIdentityAction (finiteEtaleTopology k) (finiteEtaleFrobeniusSiteIso k))

end EtaleCounterexample
