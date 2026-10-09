import EtaleCounterexample.TwoPrimaryExponent
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.Algebra.Equiv

set_option autoImplicit false
noncomputable section
open Function
namespace EtaleCounterexample
universe u v w

variable {A : Type u} {B : Type v}

theorem periodic_iterate_modEq {f : A → A} {n a b : ℕ} {x : A}
    (hx : IsPeriodicPt f n x) (h : Nat.ModEq n a b) : f^[a] x = f^[b] x := by
  calc
    f^[a] x = f^[a % n] x := (hx.iterate_mod_apply a).symm
    _ = f^[b % n] x := congrArg (fun m ↦ f^[m] x) h
    _ = f^[b] x := hx.iterate_mod_apply b

/-- The selected compatible power of a locally periodic map, defined orbitwise. -/
def twoPrimaryIterate (f : A → A) (x : A) : A :=
  f^[twoPrimaryResidue (minimalPeriod f x)] x

/-- Any positive period computes the same power; the definition is independent
of the chosen finite stage containing the point. -/
theorem twoPrimaryIterate_eq {f : A → A} {n : ℕ} {x : A}
    (hn : n ≠ 0) (hx : IsPeriodicPt f n x) :
    twoPrimaryIterate f x = f^[twoPrimaryResidue n] x := by
  exact periodic_iterate_modEq (isPeriodicPt_minimalPeriod f x)
    (twoPrimaryResidue_compatible (hx.minimalPeriod_pos (Nat.pos_of_ne_zero hn)).ne'
      hn hx.minimalPeriod_dvd).symm

theorem twoPrimaryIterate_fixed {f : A → A} {x : A} (hx : IsFixedPt f x) :
    twoPrimaryIterate f x = x := hx.iterate _

/-- Naturality for actual commuting maps, requiring periodicity only at x. -/
theorem twoPrimaryIterate_natural {f : A → A} {g : B → B} (a : A → B)
    (ha : Semiconj a f g) {n : ℕ} {x : A} (hn : n ≠ 0) (hx : IsPeriodicPt f n x) :
    a (twoPrimaryIterate f x) = twoPrimaryIterate g (a x) := by
  rw [twoPrimaryIterate_eq hn hx, twoPrimaryIterate_eq hn (hx.map ha)]
  exact ha.iterate_right _ x

theorem twoPrimaryIterate_odd {f : A → A} {n : ℕ} {x : A}
    (hn : Odd n) (hx : IsPeriodicPt f n x) : twoPrimaryIterate f x = x := by
  rw [twoPrimaryIterate_eq (by obtain ⟨a, ha⟩ := hn; omega) hx]
  exact periodic_iterate_modEq hx (twoPrimaryResidue_odd hn)

theorem twoPrimaryIterate_two {f : A → A} {x : A}
    (hx : IsPeriodicPt f 2 x) : twoPrimaryIterate f x = f x := by
  rw [twoPrimaryIterate_eq (by decide) hx]
  exact periodic_iterate_modEq hx (by simpa using twoPrimaryResidue_two_power 1)

section Algebra
variable {k : Type w} [CommRing k] [CommRing A] [Algebra k A]
  (F : A →ₐ[k] A) (hF : ∀ x : A, ∃ n : ℕ, n ≠ 0 ∧ IsPeriodicPt F n x)

/-- Compatible powers of a locally periodic algebra endomorphism are an
algebra endomorphism, proved at common periods for each pair of operands. -/
def twoPrimaryAlgHom : A →ₐ[k] A where
  toFun := twoPrimaryIterate F
  map_zero' := twoPrimaryIterate_fixed (map_zero F)
  map_one' := twoPrimaryIterate_fixed (map_one F)
  map_add' x y := by
    obtain ⟨n, hn, hx⟩ := hF x
    obtain ⟨m, hm, hy⟩ := hF y
    have hx' := hx.mul_const m
    have hy' := hy.const_mul n
    have hxy : IsPeriodicPt F (n * m) (x + y) := by
      have H := map_add (F ^ (n * m)) x y
      simp only [AlgHom.coe_pow] at H
      exact H.trans (congrArg₂ (· + ·) hx' hy')
    rw [twoPrimaryIterate_eq (Nat.mul_ne_zero hn hm) hxy,
      twoPrimaryIterate_eq (Nat.mul_ne_zero hn hm) hx',
      twoPrimaryIterate_eq (Nat.mul_ne_zero hn hm) hy']
    simpa only [AlgHom.coe_pow] using map_add (F ^ twoPrimaryResidue (n * m)) x y
  map_mul' x y := by
    obtain ⟨n, hn, hx⟩ := hF x
    obtain ⟨m, hm, hy⟩ := hF y
    have hx' := hx.mul_const m
    have hy' := hy.const_mul n
    have hxy : IsPeriodicPt F (n * m) (x * y) := by
      have H := map_mul (F ^ (n * m)) x y
      simp only [AlgHom.coe_pow] at H
      exact H.trans (congrArg₂ (· * ·) hx' hy')
    rw [twoPrimaryIterate_eq (Nat.mul_ne_zero hn hm) hxy,
      twoPrimaryIterate_eq (Nat.mul_ne_zero hn hm) hx',
      twoPrimaryIterate_eq (Nat.mul_ne_zero hn hm) hy']
    simpa only [AlgHom.coe_pow] using map_mul (F ^ twoPrimaryResidue (n * m)) x y
  commutes' r := twoPrimaryIterate_fixed (F.commutes r)

end Algebra
end EtaleCounterexample
