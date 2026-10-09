import EtaleCounterexample.FiniteEtaleComparison
import EtaleCounterexample.PointMateCalculation

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Field Ω] [IsSepClosed Ω] [Algebra k Ω]

def fieldGeometricPoint : Spec (.of Ω) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k Ω))

abbrev finiteEtaleScheme (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) : (Spec (.of k)).Etale :=
  (Scheme.AffineEtale.Spec _).obj ((finiteEtaleSpec k).obj A)

def finiteEtaleLiftToAlgHom (A : CommAlgCat.FiniteEtale.{u} k)
    (l : (Scheme.pointSmallEtale (fieldGeometricPoint k Ω)).fiber.obj
      (finiteEtaleScheme k (op A))) : A →ₐ[k] Ω where
  __ := (Scheme.Spec.preimage l.left).unop.hom
  commutes' r := by
    have h : CommRingCat.ofHom (algebraMap k A) ≫ (Scheme.Spec.preimage l.left).unop =
        CommRingCat.ofHom (algebraMap k Ω) := by
      apply Quiver.Hom.op_inj
      apply Scheme.Spec.map_injective
      change Scheme.Spec.map (Scheme.Spec.preimage l.left ≫
        (CommRingCat.ofHom (algebraMap k A)).op) = fieldGeometricPoint k Ω
      rw [CategoryTheory.Functor.map_comp, Scheme.Spec.map_preimage]
      exact CategoryTheory.Over.w l
    exact congrArg (fun a : CommRingCat.of k ⟶ CommRingCat.of Ω ↦ a.hom r) h

/-- Actual geometric lifts of an affine finite étale scheme are exactly its
algebra homomorphisms into the chosen separably closed field. -/
def finiteEtaleLiftEquiv (A : CommAlgCat.FiniteEtale.{u} k) :
    (Scheme.pointSmallEtale (fieldGeometricPoint k Ω)).fiber.obj
      (finiteEtaleScheme k (op A)) ≃ (A →ₐ[k] Ω) where
  toFun := finiteEtaleLiftToAlgHom k Ω A
  invFun a := CategoryTheory.Over.homMk (Spec.map (CommRingCat.ofHom a.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A)) = fieldGeometricPoint k Ω
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext a.comp_algebraMap)
  left_inv l := by
    apply CategoryTheory.Over.OverMorphism.ext
    exact Scheme.Spec.map_preimage l.left
  right_inv a := by
    apply AlgHom.ext
    intro x
    change (Scheme.Spec.preimage (Scheme.Spec.map (CommRingCat.ofHom a.toRingHom).op)).unop.hom x = _
    exact congrArg (fun r ↦ r.unop.hom x)
      (Scheme.Spec.preimage_map (CommRingCat.ofHom a.toRingHom).op)

/-- The full fiber comparison is natural, not merely a collection of bijections. -/
def finiteEtaleGeometricFiberIso :
    finiteEtaleSpec k ⋙ Scheme.AffineEtale.Spec _ ⋙
      (Scheme.pointSmallEtale (fieldGeometricPoint k Ω)).fiber ≅
    CommAlgCat.FiniteEtale.fiber k Ω ⋙ forget FintypeCat :=
  NatIso.ofComponents (fun A ↦ Equiv.toIso (finiteEtaleLiftEquiv k Ω A.unop)) (by
    intro A B f
    apply ConcreteCategory.hom_ext
    intro l
    apply AlgHom.ext
    intro x
    change ((Scheme.Spec.preimage
      (l.left ≫ Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))).unop.hom x) =
      ((Scheme.Spec.preimage l.left).unop.hom (f.unop.hom.hom x))
    rw [CategoryTheory.Functor.preimage_comp]
    erw [Scheme.Spec.preimage_map (CommRingCat.ofHom f.unop.hom.hom.toRingHom).op]
    rfl)

end EtaleCounterexample
