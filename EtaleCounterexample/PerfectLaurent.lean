import EtaleCounterexample.LaurentUnits
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Tactic

set_option autoImplicit false

/-!
The direct-limit Laurent ring with transition maps fixing coefficients and
sending the variable to its `p`th power. This is an algebraic construction of
`k[t^(±1/p^∞)]`. It is not asserted to be the coordinate ring of a scheme
perfection or to compute morphisms in the finite-type localization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
open LaurentPolynomial
universe u
variable (k : Type u) [Field k] (p : ℕ)

/-- The additive map multiplying integral exponents by `p^(j-i)`. -/
def exponentTransition (i j : ℕ) : ℤ →+ ℤ where
  toFun m := (p : ℤ) ^ (j - i) * m
  map_zero' := mul_zero _
  map_add' := mul_add _

/-- Constants are fixed, while `T m` maps to `T (p^(j-i) * m)`. -/
def laurentTransition (i j : ℕ) (_h : i ≤ j) : LaurentPolynomial k →+* LaurentPolynomial k :=
  AddMonoidAlgebra.mapDomainRingHom k (exponentTransition p i j)

@[simp] theorem laurentTransition_single (i j : ℕ) (h : i ≤ j) (m : ℤ) (c : k) :
    laurentTransition k p i j h (AddMonoidAlgebra.single m c) =
      AddMonoidAlgebra.single ((p : ℤ) ^ (j - i) * m) c := by
  change AddMonoidAlgebra.mapDomain (exponentTransition p i j)
    (AddMonoidAlgebra.single m c) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

instance laurentDirectedSystem :
    DirectedSystem (fun _ : ℕ ↦ LaurentPolynomial k) (fun i j h ↦ laurentTransition k p i j h) where
  map_self i x := by
    have he : exponentTransition p i i = AddMonoidHom.id ℤ := by
      apply AddMonoidHom.ext
      intro m
      simp [exponentTransition]
    simp [laurentTransition, he]
  map_map l j i hij hjl x := by
    have he : (exponentTransition p j l).comp (exponentTransition p i j) =
        exponentTransition p i l := by
      apply AddMonoidHom.ext
      intro m
      dsimp [exponentTransition]
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    have hmaps := AddMonoidAlgebra.mapDomainRingHom_comp (R := k)
      (exponentTransition p j l) (exponentTransition p i j)
    rw [he] at hmaps
    exact (congrArg (fun f : LaurentPolynomial k →+* LaurentPolynomial k ↦ f x) hmaps).symm

/-- A genuine direct limit of commutative rings, with the displayed transition maps. -/
abbrev PerfectLaurent :=
  DirectLimit (fun _ : ℕ ↦ LaurentPolynomial k) (fun i j h ↦ laurentTransition k p i j h)

/-- Inclusion of the `d`th Laurent stage. Its variable represents `t^(1/p^d)`. -/
def laurentStage (d : ℕ) : LaurentPolynomial k →+* PerfectLaurent k p :=
  DirectLimit.Ring.of (fun _ : ℕ ↦ LaurentPolynomial k)
    (fun i j h ↦ laurentTransition k p i j h) d

theorem laurentStage_injective (hp : p ≠ 0) (d : ℕ) :
    Function.Injective (laurentStage k p d) := by
  refine DirectLimit.mk_injective (fun i j h ↦ laurentTransition k p i j h) ?_ d
  intro i j hij
  change Function.Injective (AddMonoidAlgebra.mapDomain (R := k) (exponentTransition p i j))
  apply AddMonoidAlgebra.mapDomain_injective
  intro m n h
  exact mul_left_cancel₀ (pow_ne_zero _ (Int.natCast_ne_zero.mpr hp)) h

/-- Literal rational exponent corresponding to an exponent in stage `d`. -/
def rationalExponent (d : ℕ) : ℤ →+ ℚ where
  toFun m := (m : ℚ) / (p : ℚ) ^ d
  map_zero' := by simp
  map_add' := by intro a b; simp [add_div]

def rationalStage (d : ℕ) : LaurentPolynomial k →+* AddMonoidAlgebra k ℚ :=
  AddMonoidAlgebra.mapDomainRingHom k (rationalExponent p d)

theorem rationalStage_compatible (hp : p ≠ 0) (i j : ℕ) (hij : i ≤ j)
    (f : LaurentPolynomial k) :
    rationalStage k p j (laurentTransition k p i j hij f) = rationalStage k p i f := by
  have he : (rationalExponent p j).comp (exponentTransition p i j) =
      rationalExponent p i := by
    apply AddMonoidHom.ext
    intro m
    dsimp [rationalExponent, exponentTransition]
    push_cast
    have hpow : (p : ℚ) ^ j = (p : ℚ) ^ (j - i) * (p : ℚ) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hij]
    rw [hpow]
    have hp' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
    field_simp
  have hmaps := AddMonoidAlgebra.mapDomainRingHom_comp (R := k)
    (rationalExponent p j) (exponentTransition p i j)
  rw [he] at hmaps
  exact (congrArg (fun F : LaurentPolynomial k →+* AddMonoidAlgebra k ℚ ↦ F f) hmaps).symm

/-- An interpretation inside a genuine rational-exponent group algebra. -/
def rationalRealization (hp : p ≠ 0) : PerfectLaurent k p →+* AddMonoidAlgebra k ℚ :=
  DirectLimit.Ring.lift _ _ _ (rationalStage k p) (rationalStage_compatible k p hp)

theorem rationalRealization_stage (hp : p ≠ 0) (d : ℕ) (f : LaurentPolynomial k) :
    rationalRealization k p hp (laurentStage k p d f) = rationalStage k p d f := rfl

theorem rationalRealization_injective (hp : p ≠ 0) :
    Function.Injective (rationalRealization k p hp) := by
  refine DirectLimit.lift_injective (fun i j h ↦ laurentTransition k p i j h)
    (fun d ↦ rationalStage k p d)
    (fun i j hij x ↦ (rationalStage_compatible k p hp i j hij x).symm) ?_
  intro d
  change Function.Injective (AddMonoidAlgebra.mapDomain (R := k) (rationalExponent p d))
  apply AddMonoidAlgebra.mapDomain_injective
  intro m n h
  apply Int.cast_injective (α := ℚ)
  exact (div_left_inj' (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp))).mp h

/-- The relation identifying a variable in one stage with the `p`th power of
the variable in the next stage. -/
theorem laurentStage_variable (d : ℕ) :
    laurentStage k p (d + 1) (T (p : ℤ)) = laurentStage k p d (T 1) := by
  have h := DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ LaurentPolynomial k)
    (f := fun i j h ↦ laurentTransition k p i j h) (Nat.le_succ d) (T 1)
  have hs : laurentTransition k p d (d + 1) (Nat.le_succ d) (T 1) = T (p : ℤ) := by
    change laurentTransition k p d (d + 1) (Nat.le_succ d)
      (AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single (p : ℤ) 1
    rw [laurentTransition_single]
    simp
  rw [hs] at h
  exact h

/-- Every unit and its inverse occur together in a finite stage, after further
transition if necessary to witness their product as one. -/
theorem perfectLaurent_unit_from_stage (u : (PerfectLaurent k p)ˣ) :
    ∃ (d : ℕ) (f : LaurentPolynomial k), IsUnit f ∧ laurentStage k p d f = u := by
  obtain ⟨i, x, y, hx, hy⟩ := DirectLimit.exists_eq_mk₂
    (fun i j h ↦ laurentTransition k p i j h) (u : PerfectLaurent k p) (↑(u⁻¹))
  have hxy : (⟦⟨i, x * y⟩⟧ : PerfectLaurent k p) = 1 := by
    rw [← DirectLimit.mul_def, ← hx, ← hy]
    exact u.val_inv
  obtain ⟨d, hid, hd⟩ := (DirectLimit.exists_eq_one _).mp hxy
  refine ⟨d, laurentTransition k p i d hid x,
    isUnit_iff_exists_inv.mpr ⟨laurentTransition k p i d hid y, ?_⟩, ?_⟩
  · simpa only [map_mul] using hd
  · change (DirectLimit.Ring.of (fun _ : ℕ ↦ LaurentPolynomial k)
      (fun i j h ↦ laurentTransition k p i j h) d)
      (laurentTransition k p i d hid x) = u
    rw [DirectLimit.Ring.of_f]
    exact hx.symm

/-- The full unit calculation in the direct-limit Laurent ring: every unit is
`c t^(m/p^d)`, where `c ≠ 0`, `m : ℤ`, and `d : ℕ`. -/
theorem perfectLaurent_isUnit_iff (f : PerfectLaurent k p) :
    IsUnit f ↔ ∃ (c : k) (m : ℤ) (d : ℕ), c ≠ 0 ∧
      f = laurentStage k p d (LaurentPolynomial.C c * T m) := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨d, g, hg, hgu⟩ := perfectLaurent_unit_from_stage k p u
    obtain ⟨c, m, hc, rfl⟩ := (laurent_isUnit_iff g).mp hg
    exact ⟨c, m, d, hc, hgu.symm⟩
  · rintro ⟨c, m, d, hc, rfl⟩
    exact ((laurent_isUnit_iff _).mpr ⟨c, m, hc, rfl⟩).map (laurentStage k p d)

theorem rationalRealization_monomial (hp : p ≠ 0) (c : k) (m : ℤ) (d : ℕ) :
    rationalRealization k p hp (laurentStage k p d (LaurentPolynomial.C c * T m)) =
      AddMonoidAlgebra.single ((m : ℚ) / (p : ℚ) ^ d) c := by
  rw [← single_eq_C_mul_T, rationalRealization_stage]
  change AddMonoidAlgebra.mapDomain (rationalExponent p d)
    (AddMonoidAlgebra.single m c) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

/-- The unit calculation with literal rational exponents in an injective
realization, so the notation `m/p^d` is verified rather than only suggestive. -/
theorem perfectLaurent_isUnit_iff_rational (hp : p ≠ 0) (f : PerfectLaurent k p) :
    IsUnit f ↔ ∃ (c : k) (m : ℤ) (d : ℕ), c ≠ 0 ∧
      rationalRealization k p hp f =
        AddMonoidAlgebra.single ((m : ℚ) / (p : ℚ) ^ d) c := by
  rw [perfectLaurent_isUnit_iff]
  constructor
  · rintro ⟨c, m, d, hc, rfl⟩
    exact ⟨c, m, d, hc, rationalRealization_monomial k p hp c m d⟩
  · rintro ⟨c, m, d, hc, hf⟩
    refine ⟨c, m, d, hc, rationalRealization_injective k p hp ?_⟩
    rw [hf, rationalRealization_monomial]

end EtaleCounterexample
