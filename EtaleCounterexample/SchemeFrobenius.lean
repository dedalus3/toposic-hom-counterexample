import EtaleCounterexample.EtaleMorphisms
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u

/-- Frobenius only requires that `p` vanish, so this definition also works on
the zero ring of sections over the empty open. -/
def weakFrobenius (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (h : (p : R) = 0) : R →+* R where
  toFun a := a ^ p
  map_one' := one_pow p
  map_mul' a b := mul_pow a b p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' a b := by rw [add_pow_prime_eq (Fact.out : p.Prime), h]; simp

@[simp] theorem weakFrobenius_apply (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (h : (p : R) = 0) (a : R) : weakFrobenius R p h a = a ^ p := rfl

/-- Characteristic `p` on global sections implies that `p` vanishes on every
open; no nontriviality of the section ring is assumed. -/
theorem section_prime_eq_zero (X : Scheme.{u}) (p : ℕ)
    (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  simpa using congrArg (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) h

def frobeniusPresheafMap (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) : X.presheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom (weakFrobenius _ p (section_prime_eq_zero X p h U.unop))
  naturality U V f := by ext a; exact (map_pow (X.presheaf.map f).hom a p).symm

def frobeniusPresheafedHom (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) : X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 X.toTopCat
  c := frobeniusPresheafMap X p h

theorem frobeniusPresheafedHom_stalkMap (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) (x : X) (a : X.presheaf.stalk x) :
    (frobeniusPresheafedHom X p h).stalkMap x a = a ^ p := by
  obtain ⟨U, hx, b, rfl⟩ := X.presheaf.exists_germ_eq a
  have H := PresheafedSpace.stalkMap_germ_apply (frobeniusPresheafedHom X p h) U x hx b
  exact H.trans (map_pow (X.presheaf.germ U x hx).hom b p)

/-- Absolute Frobenius on the actual scheme, including its structure sheaf. -/
def schemeFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) : X ⟶ X where
  toLRSHom' :=
    { toHom := frobeniusPresheafedHom X p h
      prop := fun x ↦ {
        map_nonunit := fun a ha ↦ by
          change IsUnit ((frobeniusPresheafedHom X p h).stalkMap x a) at ha
          rw [frobeniusPresheafedHom_stalkMap] at ha
          exact isUnit_of_dvd_one (dvd_trans (dvd_pow_self a (Fact.out : p.Prime).ne_zero)
            (isUnit_iff_dvd_one.mp ha)) } }

@[simp] theorem schemeFrobenius_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) (x : X) : schemeFrobenius X p h x = x := rfl

@[simp] theorem schemeFrobenius_app (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) (a : Γ(X, U)) :
    (schemeFrobenius X p h).app U a = a ^ p := rfl

theorem schemeFrobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : ℕ) [Fact p.Prime] (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) :
    schemeFrobenius X p hX ≫ f = f ≫ schemeFrobenius Y p hY := by
  apply Scheme.Hom.ext (f := schemeFrobenius X p hX ≫ f)
    (g := f ≫ schemeFrobenius Y p hY) (by ext x; rfl)
  intro U
  change (f.app U ≫ CommRingCat.ofHom
      (weakFrobenius _ p (section_prime_eq_zero X p hX (f ⁻¹ᵁ U)))) ≫
      X.presheaf.map (𝟙 (op (f ⁻¹ᵁ U))) =
    CommRingCat.ofHom (weakFrobenius _ p (section_prime_eq_zero Y p hY U)) ≫ f.app U
  rw [CategoryTheory.Functor.map_id]
  ext a
  exact (map_pow (f.app U).hom a p).symm

theorem prime_eq_zero_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ)
    (hY : (p : Γ(Y, ⊤)) = 0) : (p : Γ(X, ⊤)) = 0 := by
  simpa using congrArg f.appTop hY

theorem schemeFrobenius_Spec (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(Spec R, ⊤)) = 0) :
    schemeFrobenius (Spec R) p h =
      Spec.map (CommRingCat.ofHom (weakFrobenius R p
        (by simpa using congrArg (Scheme.ΓSpecIso R).hom h))) := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso R).inv ≫ (schemeFrobenius (Spec R) p h).appTop =
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map _).appTop
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext a
  exact (map_pow (Scheme.ΓSpecIso R).inv.hom a p).symm

instance schemeFrobenius_surjective (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) : Surjective (schemeFrobenius X p h) :=
  ⟨fun x ↦ ⟨x, rfl⟩⟩

/-- Frobenius is universally injective. The test on all field-valued points
is proved using the actual faithfully flat field Frobenius, hence an epi of
schemes, and naturality of the structure-sheaf Frobenius. -/
theorem schemeFrobenius_universallyInjective (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (h : (p : Γ(X, ⊤)) = 0) : UniversallyInjective (schemeFrobenius X p h) := by
  apply ((tfae_universallyInjective (schemeFrobenius X p h)).out 1 2).mpr
  intro K _ f g H
  let hK := prime_eq_zero_of_hom f p h
  have hflat : Flat (schemeFrobenius (Spec (.of K)) p hK) := by
    rw [schemeFrobenius_Spec]
    exact Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField K) _)
  have : Epi (schemeFrobenius (Spec (.of K)) p hK) :=
    Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (schemeFrobenius (Spec (.of K)) p hK)).mp
  rw [schemeFrobenius_naturality f p hK h, schemeFrobenius_naturality g p hK h]
  exact H

end EtaleCounterexample
