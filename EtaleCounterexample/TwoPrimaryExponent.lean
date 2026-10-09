import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ChineseRemainder

set_option autoImplicit false
noncomputable section
namespace EtaleCounterexample

/-- A natural representative for the compatible residue that is one on the
2-primary part and zero on the odd part of a positive modulus. -/
def twoPrimaryResidue (n : ℕ) : ℕ :=
  if hn : n = 0 then 0 else
    Nat.chineseRemainder ((Nat.coprime_ordCompl Nat.prime_two hn).pow_left (n.factorization 2)) 1 0

theorem twoPrimaryResidue_twoPart {n : ℕ} (hn : n ≠ 0) :
    Nat.ModEq (2 ^ n.factorization 2) (twoPrimaryResidue n) 1 := by
  simpa only [twoPrimaryResidue, dite_eq_right hn] using
    (Nat.chineseRemainder ((Nat.coprime_ordCompl Nat.prime_two hn).pow_left
      (n.factorization 2)) 1 0).property.1

theorem twoPrimaryResidue_oddPart {n : ℕ} (hn : n ≠ 0) :
    Nat.ModEq (n / 2 ^ n.factorization 2) (twoPrimaryResidue n) 0 := by
  simpa only [twoPrimaryResidue, dite_eq_right hn] using
    (Nat.chineseRemainder ((Nat.coprime_ordCompl Nat.prime_two hn).pow_left
      (n.factorization 2)) 1 0).property.2

theorem twoPrimaryResidue_pow_two {n r : ℕ} (hn : n ≠ 0) (h : 2 ^ r ∣ n) :
    Nat.ModEq (2 ^ r) (twoPrimaryResidue n) 1 :=
  (twoPrimaryResidue_twoPart hn).of_dvd
    ((Nat.prime_two.pow_dvd_iff_dvd_ordProj hn).mp h)

theorem twoPrimaryResidue_odd_dvd {n d : ℕ} (hn : n ≠ 0)
    (hd : Odd d) (h : d ∣ n) : Nat.ModEq d (twoPrimaryResidue n) 0 :=
  (twoPrimaryResidue_oddPart hn).of_dvd
    (Nat.dvd_ordCompl_of_dvd_not_dvd h (by rintro ⟨a, ha⟩; obtain ⟨b, hb⟩ := hd; omega))

/-- Compatibility at every divisor, the defining inverse-limit condition. -/
theorem twoPrimaryResidue_compatible {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m ∣ n) : Nat.ModEq m (twoPrimaryResidue n) (twoPrimaryResidue m) := by
  have htwo := twoPrimaryResidue_pow_two hn ((Nat.ordProj_dvd m 2).trans h)
  have hodd : Odd (m / 2 ^ m.factorization 2) := by
    simpa [← even_iff_two_dvd] using (Nat.not_dvd_ordCompl Nat.prime_two hm)
  have hodd' := twoPrimaryResidue_odd_dvd hn hodd ((Nat.ordCompl_dvd m 2).trans h)
  have H := (Nat.modEq_and_modEq_iff_modEq_mul
    ((Nat.coprime_ordCompl Nat.prime_two hm).pow_left (m.factorization 2))).mp
      ⟨htwo.trans (twoPrimaryResidue_twoPart hm).symm,
        hodd'.trans (twoPrimaryResidue_oddPart hm).symm⟩
  simpa only [Nat.ordProj_mul_ordCompl_eq_self] using H

/-- All odd moduli have residue zero. -/
theorem twoPrimaryResidue_odd {n : ℕ} (hn : Odd n) :
    Nat.ModEq n (twoPrimaryResidue n) 0 :=
  twoPrimaryResidue_odd_dvd (by obtain ⟨a, ha⟩ := hn; omega) hn dvd_rfl

/-- All powers of two have residue one, including the trivial modulus one. -/
theorem twoPrimaryResidue_two_power (r : ℕ) :
    Nat.ModEq (2 ^ r) (twoPrimaryResidue (2 ^ r)) 1 :=
  twoPrimaryResidue_pow_two (pow_ne_zero _ (by decide)) dvd_rfl

end EtaleCounterexample
