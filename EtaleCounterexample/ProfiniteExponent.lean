import EtaleCounterexample.TwoPrimaryExponent
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
noncomputable section
namespace EtaleCounterexample

/-- The explicit inverse-limit presentation of profinite integers, over positive
moduli ordered by divisibility. No identification with a Galois group is assumed. -/
def CompatibleResidues :=
  { a : ∀ n : ℕ+, ZMod n // ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n),
      ZMod.castHom h (ZMod m) (a n) = a m }

/-- The specified exponent: one in every 2-primary quotient and zero in every
odd quotient. Compatibility is proved by the Chinese remainder theorem. -/
def twoPrimaryExponent : CompatibleResidues :=
  ⟨fun n ↦ (twoPrimaryResidue n : ZMod n), by
    intro m n h
    rw [map_natCast]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (twoPrimaryResidue_compatible m.ne_zero n.ne_zero h)⟩

def integralExponent (z : ℤ) : CompatibleResidues :=
  ⟨fun n ↦ (z : ZMod n), by intro m n h; exact map_intCast _ _⟩

theorem twoPrimaryExponent_odd (n : ℕ+) (hn : Odd (n : ℕ)) :
    twoPrimaryExponent.val n = 0 := by
  change (twoPrimaryResidue n : ZMod n) = 0
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (twoPrimaryResidue_odd hn)

theorem twoPrimaryExponent_two_power (r : ℕ) :
    twoPrimaryExponent.val ⟨2 ^ r, pow_pos (by decide) _⟩ = 1 := by
  change (twoPrimaryResidue (2 ^ r) : ZMod (2 ^ r)) = 1
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (twoPrimaryResidue_two_power r)

/-- This is not an ordinary integer, including a negative integer. -/
theorem twoPrimaryExponent_not_integral (z : ℤ) : twoPrimaryExponent ≠ integralExponent z := by
  intro h
  let n : ℕ+ := ⟨2 * z.natAbs + 1, by omega⟩
  have hn : Odd (n : ℕ) := ⟨z.natAbs, rfl⟩
  have hz : (z : ZMod n) = 0 := by
    rw [← show (integralExponent z).val n = (z : ZMod n) from rfl, ← h]
    exact twoPrimaryExponent_odd n hn
  have hd : (n : ℕ) ∣ z.natAbs :=
    Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have hz0 : z = 0 := by
    have : z.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hd (by dsimp [n]; omega)
    exact Int.natAbs_eq_zero.mp this
  have h2 := congrArg (fun a : CompatibleResidues ↦ a.val ⟨2, by decide⟩) h
  have h1 := twoPrimaryExponent_two_power 1
  simp only [hz0, integralExponent, Int.cast_zero] at h2
  change (twoPrimaryResidue 2 : ZMod 2) = 0 at h2
  change (twoPrimaryResidue (2 ^ 1) : ZMod (2 ^ 1)) = 1 at h1
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1)
    (h2.symm.trans (by simpa only [pow_one] using h1))

end EtaleCounterexample
