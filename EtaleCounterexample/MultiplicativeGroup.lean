import EtaleCounterexample.EtaleMorphisms
import EtaleCounterexample.SchemeLocalization
import EtaleCounterexample.LaurentUnits
import Mathlib.RingTheory.RingHom.FiniteType

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EtaleCounterexample
universe u
variable (k : Type u) [CommRing k]

/-- The actual multiplicative-group scheme in its Laurent coordinate presentation. -/
def multiplicativeGroup : Scheme.{u} := Spec (.of (LaurentPolynomial k))

def multiplicativeGroupStructure : multiplicativeGroup k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))

instance laurent_finiteType : Algebra.FiniteType k (LaurentPolynomial k) := by
  change Algebra.FiniteType k (AddMonoidAlgebra k ℤ)
  infer_instance

instance multiplicativeGroupStructure_locallyOfFiniteType :
    LocallyOfFiniteType (multiplicativeGroupStructure k) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance multiplicativeGroupStructure_quasiCompact :
    QuasiCompact (multiplicativeGroupStructure k) := by
  dsimp [multiplicativeGroupStructure, multiplicativeGroup]
  infer_instance

def multiplicativeGroupFiniteType : FiniteTypeSchemes (Spec (.of k)) :=
  MorphismProperty.Over.mk ⊤ (multiplicativeGroupStructure k)
    ⟨inferInstance, inferInstance⟩

/-- The structural geometric morphism of the actual small étale topoi. -/
def multiplicativeGroupEtaleMorphism :
    GeometricMorphism (EtaleTopos (multiplicativeGroup k)) (EtaleTopos (Spec (.of k))) :=
  affineBaseEtaleMorphism (multiplicativeGroupStructure k)

end EtaleCounterexample
