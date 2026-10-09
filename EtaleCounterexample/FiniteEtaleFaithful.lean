import EtaleCounterexample.FiniteGaloisAction
import Mathlib.RingTheory.Flat.Basic

set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- Extension of scalars to a field extension is faithful on finite étale algebras. -/
instance finiteEtaleBaseChange_faithful :
    (CommAlgCat.FiniteEtale.baseChange.{u} k Ω).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply Algebra.TensorProduct.includeRight_injective
      (A := Ω) (B := B.obj) (algebraMap k Ω).injective
    have hh := congrArg (fun m ↦ m.hom.hom (1 ⊗ₜ[k] x)) h
    simpa [CommAlgCat.FiniteEtale.baseChange] using hh

/-- Geometric fibers over a separably closed extension separate finite étale
algebra maps. This is deduced from the actual split-algebra equivalence after
faithful scalar extension. -/
instance finiteEtaleFiber_faithful [IsSepClosed Ω] :
    (CommAlgCat.FiniteEtale.fiber.{u} k Ω).Faithful :=
  Functor.Faithful.of_iso (CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber k Ω Ω).symm

/-- The constructed continuous Galois functor is faithful; fullness and
essential surjectivity remain separate obligations. -/
instance finiteEtaleContinuousGaloisFunctor_faithful [Finite k]
    [Algebra.IsAlgebraic k Ω] [IsSepClosed Ω] :
    (finiteEtaleContinuousGaloisFunctor k Ω).Faithful where
  map_injective {A B} f g h := by
    apply (CommAlgCat.FiniteEtale.fiber k Ω).map_injective
    exact congrArg (fun m ↦ m.hom.hom) h

end EtaleCounterexample
