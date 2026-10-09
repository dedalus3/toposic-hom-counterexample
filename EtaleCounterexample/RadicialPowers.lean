import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.PurelyInseparable.Basic

set_option autoImplicit false
noncomputable section
namespace EtaleCounterexample
universe u
variable (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B]

/-- Field-point injectivity forces purely inseparable fraction-field extension.
The field-point hypothesis will be supplied by the actual UH scheme theorem. -/
theorem radicial_fraction_purelyInseparable
    (h : ∀ (K : Type u) [Field K], Function.Injective
      (fun g : B →+* K ↦ g.comp (algebraMap A B))) :
    letI := FractionRing.liftAlgebra A (FractionRing B)
    IsPurelyInseparable (FractionRing A) (FractionRing B) := by
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  rw [isPurelyInseparable_iff_subsingleton_emb]
  constructor
  intro σ τ
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.injective_comp_algebraMap (A := B) (K := FractionRing B)
  apply h (AlgebraicClosure (FractionRing B))
  ext x
  change σ (algebraMap B (FractionRing B) (algebraMap A B x)) =
    τ (algebraMap B (FractionRing B) (algebraMap A B x))
  rw [← IsScalarTower.algebraMap_apply A B,
    IsScalarTower.algebraMap_apply A (FractionRing A)]
  rw [σ.commutes, τ.commutes]

variable [IsIntegrallyClosed A] [Algebra.IsIntegral A B]
  (p : ℕ) [Fact p.Prime] [CharP A p]

/-- In an integral radicial extension of a normal domain, each element has a
p-power in the base. This does not yet assert anything for nonreduced rings. -/
theorem radicial_integral_normal_pow_mem
    (h : ∀ (K : Type u) [Field K], Function.Injective
      (fun g : B →+* K ↦ g.comp (algebraMap A B))) (b : B) :
    ∃ n : ℕ, b ^ (p ^ n) ∈ (algebraMap A B).range := by
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  have : IsPurelyInseparable (FractionRing A) (FractionRing B) :=
    radicial_fraction_purelyInseparable A B h
  obtain ⟨n, r, hr⟩ := IsPurelyInseparable.pow_mem (FractionRing A) p
    (algebraMap B (FractionRing B) b)
  have hb : IsIntegral A ((algebraMap B (FractionRing B) b) ^ (p ^ n)) :=
    ((Algebra.IsIntegral.isIntegral b).map (IsScalarTower.toAlgHom A B (FractionRing B))).pow _
  rw [← hr] at hb
  have hrint : IsIntegral A r := isIntegral_algebraMap_iff.mp hb
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hrint
  refine ⟨n, a, ?_⟩
  apply IsFractionRing.injective B (FractionRing B)
  rw [map_pow, ← hr, ← ha, ← IsScalarTower.algebraMap_apply A B,
    ← IsScalarTower.algebraMap_apply A (FractionRing A)]

section Nonreduced
variable (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
  [(nilradical B).IsPrime] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- Removing the nilradical and then killing the resulting nilpotent error
extends the power-descent statement to a nonreduced source. -/
theorem radicial_integral_normal_pow_mem_nonreduced
    (hinj : Function.Injective (algebraMap A (B ⧸ nilradical B)))
    (h : ∀ (K : Type u) [Field K], Function.Injective
      (fun g : B →+* K ↦ g.comp (algebraMap A B))) (b : B) :
    ∃ n : ℕ, b ^ (p ^ n) ∈ (algebraMap A B).range := by
  let : FaithfulSMul A (B ⧸ nilradical B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let : Algebra.IsIntegral A (B ⧸ nilradical B) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ A _) Ideal.Quotient.mk_surjective
  have hQ : ∀ (K : Type u) [Field K], Function.Injective
      (fun g : (B ⧸ nilradical B) →+* K ↦ g.comp (algebraMap A (B ⧸ nilradical B))) := by
    intro K _ g g' he
    have H : g.comp (Ideal.Quotient.mk _) = g'.comp (Ideal.Quotient.mk _) :=
      h K he
    apply RingHom.ext
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact RingHom.congr_fun H b
  obtain ⟨n, a, ha⟩ := radicial_integral_normal_pow_mem A (B ⧸ nilradical B) p hQ
    (Ideal.Quotient.mk _ b)
  have he : Ideal.Quotient.mk (nilradical B) (algebraMap A B a) =
      Ideal.Quotient.mk (nilradical B) (b ^ (p ^ n)) := by
    simpa only [map_pow, IsScalarTower.algebraMap_apply A B (B ⧸ nilradical B),
      Ideal.Quotient.algebraMap_eq] using ha
  have hn : IsNilpotent (algebraMap A B a - b ^ (p ^ n)) :=
    mem_nilradical.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he)
  obtain ⟨d, hd⟩ := hn
  have hd' : (algebraMap A B a - b ^ (p ^ n)) ^ (p ^ d) = 0 :=
    pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hd
  rw [sub_pow_char_pow, sub_eq_zero, ← pow_mul, ← pow_add] at hd'
  exact ⟨n + d, a ^ (p ^ d), (map_pow _ _ _).trans hd'⟩
end Nonreduced

end EtaleCounterexample
