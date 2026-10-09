import EtaleCounterexample.Obstruction
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.AlgebraicClosure

set_option autoImplicit false

/-!
Unconditional finite-field ingredients, plus a clearly conditional obstruction.
No profinite exponent or global Galois automorphism is constructed in this file.
-/

noncomputable section
namespace EtaleCounterexample
universe u v
variable (k : Type u) [Field k] [Finite k]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

/-- Elements fixed by a positive odd power of the `q`-power map. -/
def oddDegreeElements : Set Ω :=
  {z | ∃ n : ℕ, Odd n ∧ z ^ (Nat.card k ^ n) = z}

include p in
/-- The odd-degree locus is infinite, proved by embedding actual finite field
extensions of arbitrarily large odd degree into the algebraically closed field. -/
theorem oddDegreeElements_infinite : (oddDegreeElements k Ω).Infinite := by
  intro hfin
  let := hfin.fintype
  let n := 2 * Nat.card (oddDegreeElements k Ω) + 1
  have hn : Odd n := ⟨Nat.card (oddDegreeElements k Ω), rfl⟩
  have : NeZero n := ⟨by dsimp [n]; omega⟩
  let f : FiniteField.Extension k p n →ₐ[k] Ω := IsAlgClosed.lift
  let j : FiniteField.Extension k p n → oddDegreeElements k Ω := fun x ↦
    ⟨f x, n, hn, by
      rw [← map_pow]
      congr 1
      let := Fintype.ofFinite (FiniteField.Extension k p n)
      rw [← FiniteField.natCard_extension k p n, ← Fintype.card_eq_nat_card]
      exact FiniteField.pow_card x⟩
  have hj : Function.Injective j := by
    intro x y h
    exact f.injective (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective j hj
  rw [FiniteField.natCard_extension] at hcard
  have hpow : n < Nat.card k ^ n := Nat.lt_pow_self Finite.one_lt_card
  dsimp only [n] at hpow hcard
  omega

include p in
/-- Removing zero still leaves infinitely many nonzero odd-degree elements. -/
theorem oddDegreeElements_nonzero_infinite :
    (oddDegreeElements k Ω \ {0}).Infinite :=
  (oddDegreeElements_infinite k p Ω).sdiff (Set.finite_singleton 0)

/-- Arithmetic Frobenius acts nontrivially on the actual quadratic extension. -/
theorem quadratic_frobenius_moves :
    ∃ z : FiniteField.Extension k p 2, z ≠ 0 ∧ z ^ Nat.card k ≠ z := by
  let := Fintype.ofFinite k
  have ho : orderOf (FiniteField.Extension.frob k p 2) = 2 := by
    simpa [FiniteField.Extension.frob, FiniteField.finrank_extension] using
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k (FiniteField.Extension k p 2)
  have hne : FiniteField.Extension.frob k p 2 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    omega
  have hm : ∃ z, FiniteField.Extension.frob k p 2 z ≠ z := by
    by_contra! h
    apply hne
    ext z
    exact h z
  obtain ⟨z, hz⟩ := hm
  refine ⟨z, ?_, ?_⟩
  · intro h
    subst z
    exact hz (map_zero _)
  · simpa using hz

/-- Characteristic two is included, with no assumption that two is invertible. -/
theorem characteristic_two_quadratic_moves :
    ∃ z : FiniteField.Extension (ZMod 2) 2 2, z ≠ 0 ∧ z ^ 2 ≠ z := by
  simpa using quadratic_frobenius_moves (ZMod 2) 2

/-- Conditional on a global automorphism with the proposed fixed and moved
points, the obstruction holds for every integer exponent and every `p^d`
denominator. The existence of that automorphism is not assumed silently. -/
theorem no_monomial_of_odd_fixed [CharP Ω p]
    (σ : Ω ≃+* Ω)
    (hfix : ∀ z ∈ oddDegreeElements k Ω, σ z = z)
    (hne : ∃ z, σ z ≠ z) (d : ℕ) :
    ¬ ∃ (c : Ω) (m : ℤ), ∀ z : Ω, z ≠ 0 →
      (σ z) ^ (p ^ d) = c * z ^ m := by
  apply no_monomial_of_infinite_fixed σ (oddDegreeElements_nonzero_infinite k p Ω)
    (fun z hz ↦ by simpa using hz.2) (fun z hz ↦ hfix z hz.1) hne (p ^ d)
  exact iterateFrobenius_inj Ω p d

end EtaleCounterexample
