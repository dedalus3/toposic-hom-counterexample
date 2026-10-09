import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Associated

set_option autoImplicit false

/-!
Units at one Laurent-polynomial stage. The common-stage/direct-limit argument
and the comparison with scheme perfection are not supplied by this file.
-/

namespace EtaleCounterexample
open Polynomial LaurentPolynomial
universe u
variable {k : Type u} [Field k]

/-- Every unit of the actual Laurent polynomial ring over a field is a nonzero
constant times an integral (possibly negative) power of its variable. -/
theorem laurent_isUnit_iff (f : LaurentPolynomial k) :
    IsUnit f ↔ ∃ (c : k) (m : ℤ), c ≠ 0 ∧ f = LaurentPolynomial.C c * T m := by
  constructor
  · intro hf
    induction f using LaurentPolynomial.induction_on_mul_T with
    | mul_T f n =>
      have hf' : IsUnit (algebraMap k[X] (LaurentPolynomial k) f) :=
        (IsUnit.mul_iff.mp hf).1
      obtain ⟨N, hN⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (X : k[X])).mp hf'
      obtain ⟨r, _, hfr⟩ := (dvd_prime_pow (Polynomial.prime_X (R := k)) N).mp hN
      obtain ⟨u, hu⟩ := hfr.symm
      obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
      refine ⟨c, (r : ℤ) - n, hc.ne_zero, ?_⟩
      rw [← hu, ← hcu, map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C]
      simp only [T_add, sub_eq_add_neg]
      ac_rfl
  · rintro ⟨c, m, hc, rfl⟩
    exact ((isUnit_iff_ne_zero.mpr hc).map LaurentPolynomial.C).mul (isUnit_T m)

end EtaleCounterexample
