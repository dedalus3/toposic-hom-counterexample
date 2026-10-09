import EtaleCounterexample.EtaleMorphisms
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Finiteness.Cardinality

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k : Type u) [Field k]

instance finiteEtaleSpec_isEtale (A : CommAlgCat.FiniteEtale.{u} k) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- Finite étale algebras as actual objects of the affine étale site. -/
def finiteEtaleSpec : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ (Spec (.of k)).AffineEtale where
  obj A := Scheme.AffineEtale.mk (Spec.map (CommRingCat.ofHom (algebraMap k A.unop)))
  map g := MorphismProperty.CostructuredArrow.homMk
    (CommRingCat.ofHom g.unop.hom.hom.toRingHom).op trivial (by
      erw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (g.unop.hom.hom.comp_algebraMap))
  map_id A := by
    apply MorphismProperty.Comma.Hom.ext
    · apply Quiver.Hom.unop_inj
      rfl
    · subsingleton
  map_comp f g := by
    apply MorphismProperty.Comma.Hom.ext
    · apply Quiver.Hom.unop_inj
      rfl
    · subsingleton

/-- The ring map of an affine étale object, recovered by full faithfulness of Spec. -/
def affineEtaleStructureMap (A : (Spec (.of k)).AffineEtale) :
    k →+* A.left.unop :=
  (Scheme.Spec.preimage A.hom).unop.hom

instance affineEtaleCoordinateAlgebra (A : (Spec (.of k)).AffineEtale) :
    Algebra k A.left.unop := (affineEtaleStructureMap k A).toAlgebra

instance affineEtaleCoordinateEtale (A : (Spec (.of k)).AffineEtale) :
    Algebra.Etale k A.left.unop := by
  apply RingHom.etale_algebraMap.mp
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
  change Etale (Scheme.Spec.map (Scheme.Spec.preimage A.hom))
  rw [Scheme.Spec.map_preimage]
  exact A.prop

instance affineEtaleCoordinateFinite (A : (Spec (.of k)).AffineEtale) :
    Module.Finite k A.left.unop := Algebra.FormallyUnramified.finite_of_free k A.left.unop

theorem affineEtaleCoordinates_finite [Finite k] (A : (Spec (.of k)).AffineEtale) :
    Finite A.left.unop := Module.finite_of_finite k

def finiteEtaleSpecHom {A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ}
    (g : (finiteEtaleSpec k).obj A ⟶ (finiteEtaleSpec k).obj B) :
    B.unop →ₐ[k] A.unop where
  __ := g.left.unop.hom
  commutes' r := by
    have h : CommRingCat.ofHom (algebraMap k B.unop) ≫ g.left.unop =
        CommRingCat.ofHom (algebraMap k A.unop) := by
      apply Quiver.Hom.op_inj
      apply Scheme.Spec.map_injective
      simpa [Functor.map_comp, finiteEtaleSpec] using g.w
    exact congrArg (fun a : CommRingCat.of k ⟶ CommRingCat.of A.unop ↦ a.hom r) h

def finiteEtaleSpecFullyFaithful : (finiteEtaleSpec k).FullyFaithful where
  preimage g := (ObjectProperty.homMk (CommAlgCat.ofHom (finiteEtaleSpecHom k g))).op
  map_preimage g := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply Quiver.Hom.unop_inj
    rfl
  preimage_map g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    rfl

instance : (finiteEtaleSpec k).Full := (finiteEtaleSpecFullyFaithful k).full
instance : (finiteEtaleSpec k).Faithful := (finiteEtaleSpecFullyFaithful k).faithful

instance finiteEtaleSpec_essSurj : (finiteEtaleSpec k).EssSurj where
  mem_essImage A := by
    refine ⟨op (CommAlgCat.FiniteEtale.of k A.left.unop), ⟨?_⟩⟩
    refine MorphismProperty.CostructuredArrow.isoMk (Iso.refl A.left) trivial trivial ?_
    change Scheme.Spec.map (𝟙 A.left) ≫ A.hom =
      Spec.map (CommRingCat.ofHom (affineEtaleStructureMap k A))
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    simpa [affineEtaleStructureMap] using (Scheme.Spec.map_preimage A.hom).symm

instance finiteEtaleSpec_isEquivalence : (finiteEtaleSpec k).IsEquivalence where

/-- The actual affine étale site over a field is the opposite category of
finite étale algebras. This is a proved scheme/algebra comparison. -/
abbrev finiteEtaleAffineEquivalence :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ≌ (Spec (.of k)).AffineEtale :=
  (finiteEtaleSpec k).asEquivalence

/-- The topology is transported from the actual affine étale topology. -/
abbrev finiteEtaleTopology : GrothendieckTopology (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ :=
  (finiteEtaleSpec k).inducedTopology (Scheme.AffineEtale.topology (Spec (.of k)))

/-- An unconditional equivalence to actual étale sheaves, at the finite-étale-
algebra stage of the Galois comparison. The topology is not replaced by a toy model. -/
def finiteEtaleSheafEquivalence :
    Sheaf (finiteEtaleTopology k) (Type u) ≌ EtaleTopos (Spec (.of k)) := by
  letI : (finiteEtaleAffineEquivalence k).symm.inverse.IsDenseSubsite
      (finiteEtaleTopology k) (Scheme.AffineEtale.topology (Spec (.of k))) := by
    change (finiteEtaleSpec k).IsDenseSubsite _ _
    infer_instance
  exact
  ((finiteEtaleAffineEquivalence k).symm.sheafCongr
    (Scheme.AffineEtale.topology (Spec (.of k))) (finiteEtaleTopology k) (Type u)).symm.trans
    (Scheme.AffineEtale.sheafEquiv _ _)

end EtaleCounterexample
