import EtaleCounterexample.BaseEtaleCoordinates
import EtaleCounterexample.NonintegralField
import Mathlib.RingTheory.Etale.StandardEtale

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample

/-- An actual standard étale Z-algebra containing the simple roots of
`X^(p^n)-X` in characteristic p. Inverting the derivative makes it étale over Z. -/
def integerFrobeniusEtalePair (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    StandardEtalePair ℤ where
  f := X ^ (p ^ n) - X
  monic_f := monic_X_pow_sub (by
    have hp : 1 < p ^ n := one_lt_pow₀ (Fact.out : p.Prime).one_lt hn
    rw [degree_X]
    exact_mod_cast hp)
  g := derivative (X ^ (p ^ n) - X)
  cond := ⟨1, 0, 1, by simp⟩

theorem integerFrobeniusEtalePair_hasMap (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (Ω : Type) [Field Ω] [CharP Ω p] (z : Ω) (hz : z ^ (p ^ n) = z) :
    (integerFrobeniusEtalePair p n hn).HasMap z := by
  constructor
  · simpa [integerFrobeniusEtalePair, map_sub, map_pow] using sub_eq_zero.mpr hz
  · have hcast : ((p ^ n : ℕ) : Ω) = 0 := by
      rw [Nat.cast_pow, CharP.cast_eq_zero Ω p, zero_pow hn]
    simpa [integerFrobeniusEtalePair, derivative_sub, derivative_X_pow, derivative_X,
      hcast, zero_pow hn] using (isUnit_one : IsUnit (1 : Ω)).neg

variable (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsSepClosed Ω]
  [Algebra (ZMod p) Ω] [Algebra.IsAlgebraic (ZMod p) Ω] [CharP Ω p]

def arithmeticBasePoint : Spec (.of Ω) ⟶ Spec (.of ℤ) :=
  fieldGeometricPoint (ZMod p) Ω ≫ primeBase p

theorem arithmeticBasePoint_eq : arithmeticBasePoint p Ω =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  rw [arithmeticBasePoint, fieldGeometricPoint, primeBase, ← Spec.map_comp]
  congr 1
  ext n
  simp

/-- Each algebraic coordinate occurs as a section on an actual étale
neighborhood over Spec Z. This is not a postulated lifting of finite fields. -/
theorem arithmetic_exists_etale_coordinate (z : Ω) :
    ∃ (U : (Spec (.of ℤ)).Etale)
      (l : (Scheme.pointSmallEtale (arithmeticBasePoint p Ω)).fiber.obj U)
      (r : Γ(U.left, ⊤)), geometricSectionValue l.left r = z := by
  obtain ⟨n, hn, hz⟩ := finiteFieldFrobenius_locallyPeriodic (ZMod p) Ω z
  have hz' : z ^ (p ^ n) = z := by
    simpa only [Function.IsPeriodicPt, Function.IsFixedPt, FiniteField.coe_frobeniusAlgHom,
      pow_iterate, ZMod.card] using hz
  let P := integerFrobeniusEtalePair p n hn
  let b := P.lift z (integerFrobeniusEtalePair_hasMap p n hn Ω z hz')
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap ℤ P.Ring))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let U : (Spec (.of ℤ)).Etale := .mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ P.Ring)))
  let l : (Scheme.pointSmallEtale (arithmeticBasePoint p Ω)).fiber.obj U :=
    Over.homMk (Spec.map (CommRingCat.ofHom b.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom b.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ P.Ring)) = arithmeticBasePoint p Ω
      rw [← Spec.map_comp, arithmeticBasePoint_eq]
      congr 1
      exact CommRingCat.hom_ext b.comp_algebraMap)
  refine ⟨U, l, (Scheme.ΓSpecIso (.of P.Ring)).inv P.X, ?_⟩
  exact (geometricSectionValue_spec (CommRingCat.ofHom b.toRingHom) P.X).trans
    (P.lift_X z (integerFrobeniusEtalePair_hasMap p n hn Ω z hz'))

/-- Arithmetic relative isomorphisms of G_m geometric points force equality
of coordinates, proved using genuine étale neighborhoods over Spec Z. -/
theorem arithmetic_relative_multiplicativeGroupPoint_eq (z w : Ωˣ)
    (γ : (etalePoint (multiplicativeGroupPoint (ZMod p) Ω z)).directImage ≅
      (etalePoint (multiplicativeGroupPoint (ZMod p) Ω w)).directImage)
    (hγ : RelativeCompatible
      (relativeEtalePoint (multiplicativeGroupStructure (ZMod p) ≫ primeBase p)
        (multiplicativeGroupPoint (ZMod p) Ω z)
        (show _ = arithmeticBasePoint p Ω by
          rw [← Category.assoc, multiplicativeGroupPoint_over]; rfl))
      (relativeEtalePoint (multiplicativeGroupStructure (ZMod p) ≫ primeBase p)
        (multiplicativeGroupPoint (ZMod p) Ω w)
        (show _ = arithmeticBasePoint p Ω by
          rw [← Category.assoc, multiplicativeGroupPoint_over]; rfl)) γ) : z = w := by
  obtain ⟨U, l, r, hr⟩ := arithmetic_exists_etale_coordinate p Ω (z : Ω)
  exact relativePoint_eq_of_baseEtale_coordinate (ZMod p) Ω _ _ U l r z w hr _ _ γ hγ

end EtaleCounterexample
