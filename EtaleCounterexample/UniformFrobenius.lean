import EtaleCounterexample.AffineUHPowers
import Mathlib.RingTheory.FiniteType

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace EtaleCounterexample
universe u
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  (p : ℕ) [Fact p.Prime] [CharP B p]

def powerInRangeSubalgebra (n : ℕ) : Subalgebra A B where
  carrier := {b | b ^ (p ^ n) ∈ (algebraMap A B).range}
  zero_mem' := by
    change (0 : B) ^ (p ^ n) ∈ (algebraMap A B).range
    rw [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
    exact (algebraMap A B).range.zero_mem
  one_mem' := by
    change (1 : B) ^ (p ^ n) ∈ (algebraMap A B).range
    rw [one_pow]
    exact (algebraMap A B).range.one_mem
  add_mem' hx hy := by
    change (_ + _) ^ (p ^ n) ∈ (algebraMap A B).range
    rw [add_pow_char_pow]
    exact (algebraMap A B).range.add_mem hx hy
  mul_mem' hx hy := by
    change (_ * _) ^ (p ^ n) ∈ (algebraMap A B).range
    rw [mul_pow]
    exact (algebraMap A B).range.mul_mem hx hy
  algebraMap_mem' a := ⟨a ^ (p ^ n), map_pow _ _ _⟩

omit [Fact p.Prime] [CharP B p] in
theorem pow_mem_range_mono {b : B} {n N : ℕ} (hn : n ≤ N)
    (h : b ^ (p ^ n) ∈ (algebraMap A B).range) :
    b ^ (p ^ N) ∈ (algebraMap A B).range := by
  rw [← Nat.add_sub_of_le hn, pow_add, pow_mul]
  exact (algebraMap A B).range.pow_mem h _

/-- Finite type makes the pointwise p-power descent exponent uniform over
the entire source algebra, including its nilpotents. -/
theorem finiteType_uniform_pow_mem [Algebra.FiniteType A B]
    (h : ∀ b : B, ∃ n : ℕ, b ^ (p ^ n) ∈ (algebraMap A B).range) :
    ∃ N : ℕ, ∀ b : B, b ^ (p ^ N) ∈ (algebraMap A B).range := by
  classical
  choose n hn using h
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := A) (A := B))
  refine ⟨s.sup n, ?_⟩
  have hle : Algebra.adjoin A (s : Set B) ≤ powerInRangeSubalgebra A B p (s.sup n) := by
    apply Algebra.adjoin_le
    intro b hb
    exact pow_mem_range_mono A B p (Finset.le_sup hb) (hn b)
  intro b
  exact hle (by rw [hs]; trivial)

/-- Descending a single uniform Frobenius through an injective ring map. -/
def descendedFrobenius (φ : A →+* B) (hi : Function.Injective φ) (n : ℕ)
    (h : ∀ b : B, b ^ (p ^ n) ∈ φ.range) : B →+* A where
  toFun b := (h b).choose
  map_one' := hi (by rw [(h 1).choose_spec, one_pow, map_one])
  map_zero' := hi (by rw [(h 0).choose_spec, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), map_zero])
  map_add' a b := hi (by rw [(h (a + b)).choose_spec, map_add,
    (h a).choose_spec, (h b).choose_spec, add_pow_char_pow])
  map_mul' a b := hi (by rw [(h (a * b)).choose_spec, map_mul,
    (h a).choose_spec, (h b).choose_spec, mul_pow])

omit [Algebra A B] in
@[simp] theorem descendedFrobenius_apply (φ : A →+* B) (hi : Function.Injective φ) (n : ℕ)
    (h : ∀ b : B, b ^ (p ^ n) ∈ φ.range) (b : B) :
    φ (descendedFrobenius A B p φ hi n h b) = b ^ (p ^ n) := (h b).choose_spec

omit [Algebra A B] in
theorem descendedFrobenius_comp (φ : A →+* B) (hi : Function.Injective φ) (n : ℕ)
    (h : ∀ b : B, b ^ (p ^ n) ∈ φ.range) (a : A) :
    descendedFrobenius A B p φ hi n h (φ a) = a ^ (p ^ n) := by
  apply hi
  rw [descendedFrobenius_apply, map_pow]

variable [IsDomain A] [IsIntegrallyClosed A] [CharP A p] [Algebra.FiniteType A B]

/-- Every finite-type actual affine UH over a normal domain admits a genuine
ring homomorphism in the other direction whose two composites are one fixed
iterate of Frobenius. This includes nonreduced source algebras. -/
theorem affineUH_frobeniusFactorization
    (h : universalHomeomorphisms (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    ∃ (n : ℕ) (ψ : B →+* A),
      (algebraMap A B).comp ψ = iterateFrobenius B p n ∧
      ψ.comp (algebraMap A B) = iterateFrobenius A p n := by
  have hi : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply affineUH_reduction_injective A B h
    exact congrArg (algebraMap B (B ⧸ nilradical B)) hab
  obtain ⟨n, hn⟩ := finiteType_uniform_pow_mem A B p (affineUH_pow_mem A B p h)
  refine ⟨n, descendedFrobenius A B p (algebraMap A B) hi n hn, ?_, ?_⟩
  · ext b; exact descendedFrobenius_apply A B p _ hi n hn b
  · ext a; exact descendedFrobenius_comp A B p _ hi n hn a

end EtaleCounterexample
