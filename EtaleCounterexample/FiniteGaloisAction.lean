import EtaleCounterexample.FiniteEtaleFibers
import EtaleCounterexample.FiniteFieldBaseTwist
import Mathlib.CategoryTheory.Galois.ContAction
import Mathlib.FieldTheory.KrullTopology

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite FintypeCatDiscrete
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
/-- Central elements act naturally on finite discrete continuous actions. -/
def centralFiniteContinuousActionIso {G : Type u} [Group G] [TopologicalSpace G]
    (g : G) (hg : ∀ h, g * h = h * g) :
    𝟭 (ContAction FintypeCat.{u} G) ≅ 𝟭 (ContAction FintypeCat.{u} G) :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _
    ((centralActionIso (V := FintypeCat.{u}) g hg).app A.obj)) (by
      intro A B f
      apply ObjectProperty.hom_ext
      exact (centralActionIso (V := FintypeCat.{u}) g hg).hom.naturality f.hom)

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- The actual Galois group acts on finite étale geometric fibers by postcomposition. -/
def finiteEtaleGaloisAction (A : CommAlgCat.FiniteEtale.{u} k) :
    Action FintypeCat.{u} (Ω ≃ₐ[k] Ω) where
  V := (CommAlgCat.FiniteEtale.fiber k Ω).obj (op A)
  ρ :=
    { toFun := fun σ ↦ FintypeCat.homMk (fun a ↦ σ.toAlgHom.comp a)
      map_one' := by apply FintypeCat.hom_ext; intro a; apply AlgHom.ext; intro x; rfl
      map_mul' := by
        intro σ τ
        apply FintypeCat.hom_ext
        intro a
        apply AlgHom.ext
        intro x
        rfl }

def finiteEtaleGaloisActionFunctor :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ Action FintypeCat.{u} (Ω ≃ₐ[k] Ω) where
  obj A := finiteEtaleGaloisAction k Ω A.unop
  map f :=
    { hom := (CommAlgCat.FiniteEtale.fiber k Ω).map f
      comm σ := by apply FintypeCat.hom_ext; intro a; rfl }
  map_id := by intro A; rfl
  map_comp := by intro A B C f g; rfl

variable [Finite k] [Algebra.IsAlgebraic k Ω]

/-- The Galois action is continuous for the actual Krull topology, with discrete
finite fibers. An open subgroup fixing all finitely many fiber coordinates
acts trivially. -/
theorem finiteEtaleGaloisAction_continuous (A : CommAlgCat.FiniteEtale.{u} k) :
    (finiteEtaleGaloisAction k Ω A).IsContinuous := by
  have : Finite A := Module.finite_of_finite k
  let H : OpenSubgroup (Ω ≃ₐ[k] Ω) := OpenSubgroup.iInfOfFinite
    (fun x : (A →ₐ[k] Ω) × A ↦
      ⟨MulAction.stabilizer (Ω ≃ₐ[k] Ω) (x.1 x.2),
        stabilizer_isOpen_of_isIntegral (x.1 x.2)⟩)
  apply Action.trivialOnSet_le_isContinuous H
  intro σ hσ
  apply ConcreteCategory.hom_ext
  intro a
  apply AlgHom.ext
  intro x
  exact OpenSubgroup.iInfOfFinite_le _ (a, x) hσ

/-- A functor into actual finite discrete continuous Galois sets.
Full faithfulness, essential surjectivity, and the topology comparison are not
asserted here. -/
def finiteEtaleContinuousGaloisFunctor :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ ContAction FintypeCat.{u} (Ω ≃ₐ[k] Ω) :=
  ObjectProperty.lift _ (finiteEtaleGaloisActionFunctor k Ω)
    (fun A ↦ finiteEtaleGaloisAction_continuous k Ω A.unop)

/-- This continuous action functor has the actual geometric fiber as its
underlying set-valued functor. -/
def finiteEtaleContinuousGeometricFiberIso [IsSepClosed Ω] :
    finiteEtaleSpec k ⋙ Scheme.AffineEtale.Spec _ ⋙
      (Scheme.pointSmallEtale (fieldGeometricPoint k Ω)).fiber ≅
    finiteEtaleContinuousGaloisFunctor k Ω ⋙ forget _ :=
  finiteEtaleGeometricFiberIso k Ω

variable [Fintype k]

omit [Finite k] in
/-- Arithmetic Frobenius is central in the actual automorphism group. -/
theorem arithmeticFrobenius_central (σ : Ω ≃ₐ[k] Ω) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k Ω * σ =
      σ * FiniteField.frobeniusAlgEquivOfAlgebraic k Ω := by
  ext x
  exact (map_pow σ x (Fintype.card k)).symm

/-- The Frobenius natural automorphism on actual finite continuous Galois sets. -/
def arithmeticFrobeniusContinuousActionIso :
    𝟭 (ContAction FintypeCat.{u} (Ω ≃ₐ[k] Ω)) ≅
    𝟭 (ContAction FintypeCat.{u} (Ω ≃ₐ[k] Ω)) :=
  centralFiniteContinuousActionIso (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
    (arithmeticFrobenius_central k Ω)

omit [Finite k] in
/-- Arithmetic Frobenius in the Galois action agrees with the site Frobenius.
This fixes the action convention on actual finite étale geometric fibers. -/
theorem finiteEtaleGaloisAction_frobenius (A : CommAlgCat.FiniteEtale.{u} k)
    (a : A →ₐ[k] Ω) :
    ConcreteCategory.hom ((finiteEtaleGaloisAction k Ω A).ρ
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) a =
    a.comp (finiteEtaleFrobenius k A).toAlgHom := by
  apply AlgHom.ext
  intro x
  exact (map_pow a x (Fintype.card k)).symm

end EtaleCounterexample
