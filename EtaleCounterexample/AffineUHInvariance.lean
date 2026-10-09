import EtaleCounterexample.RelativeFrobenius
import EtaleCounterexample.UniformFrobenius
import EtaleCounterexample.EtaleComposition
import EtaleCounterexample.LaurentUH
import EtaleCounterexample.SchemeRoofs

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u

def etaleBaseChangeIdIso (X : Scheme.{u}) : etaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.Over.isoMk (asIso (pullback.fst U.hom (𝟙 X)))
      (by simp [pullback.condition])) (by
    intro U V a
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (pullback.fst U.hom (𝟙 X) ≫ a.left)
      (pullback.snd U.hom (𝟙 X)) _ ≫ pullback.fst V.hom (𝟙 X) = _
    exact pullback.lift_fst ..)

def etaleDirectImageIdIso (X : Scheme.{u}) : etaleDirectImage (𝟙 X) ≅ 𝟭 (EtaleTopos X) := by
  letI := etaleBaseChange_continuous (𝟙 X)
  exact Functor.sheafPushforwardContinuousId' (etaleBaseChangeIdIso X)
    (Type u) X.smallEtaleTopology

def etaleDirectImageSchemeIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    EtaleTopos X ≌ EtaleTopos Y :=
  CategoryTheory.Equivalence.mk (etaleDirectImage e.hom) (etaleDirectImage e.inv)
    (etaleDirectImageCompIso e.hom e.inv ≪≫
      eqToIso (congrArg etaleDirectImage e.hom_inv_id) ≪≫ etaleDirectImageIdIso X).symm
    (etaleDirectImageCompIso e.inv e.hom ≪≫
      eqToIso (congrArg etaleDirectImage e.inv_hom_id) ≪≫ etaleDirectImageIdIso Y)

instance etaleDirectImage_isEquivalence_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : (etaleDirectImage f).IsEquivalence :=
  (etaleDirectImageSchemeIso (asIso f)).isEquivalence_functor

def affineFrobeniusEtaleIso (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    etaleDirectImage (Spec.map (CommRingCat.ofHom (frobenius R p))) ≅
      𝟭 (EtaleTopos (Spec (.of R))) := by
  let h : (p : Γ(Spec (.of R), ⊤)) = 0 := by
    have H := congrArg (Scheme.ΓSpecIso (.of R)).inv.hom (CharP.cast_eq_zero R p)
    simpa only [map_natCast, map_zero] using H
  have H : schemeFrobenius (Spec (.of R)) p h =
      Spec.map (CommRingCat.ofHom (frobenius R p)) := by
    rw [schemeFrobenius_Spec]
    rfl
  exact eqToIso (congrArg etaleDirectImage H.symm) ≪≫ schemeFrobeniusEtaleDirectImageIso p h

/-- Every iterate of absolute Frobenius has actual étale direct image
naturally isomorphic to the identity. -/
def affineIterateFrobeniusEtaleIso (R : Type u) [CommRing R] (p : ℕ)
    [Fact p.Prime] [CharP R p] (n : ℕ) :
    etaleDirectImage (Spec.map (CommRingCat.ofHom (iterateFrobenius R p n))) ≅
      𝟭 (EtaleTopos (Spec (.of R))) := by
  induction n with
  | zero => simpa using etaleDirectImageIdIso (Spec (.of R))
  | succ n ih =>
    have H : Spec.map (CommRingCat.ofHom (iterateFrobenius R p (n + 1))) =
        Spec.map (CommRingCat.ofHom (frobenius R p)) ≫
          Spec.map (CommRingCat.ofHom (iterateFrobenius R p n)) := by
      rw [Nat.add_comm n 1, iterateFrobenius_add, iterateFrobenius_one, ← Spec.map_comp]
      rfl
    exact eqToIso (congrArg etaleDirectImage H) ≪≫
      (etaleDirectImageCompIso _ _).symm ≪≫
      isoWhiskerRight (affineFrobeniusEtaleIso R p) _ ≪≫
      (etaleDirectImage _).leftUnitor ≪≫ ih

/-- Étale invariance for every actual finite-type affine UH over a normal
domain. The proof uses the uniform Frobenius factorization, not an assumption
of invariance or agreement on geometric points. -/
theorem affineUH_etaleDirectImage_isEquivalence
    (A B : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    (h : universalHomeomorphisms (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    (etaleDirectImage (Spec.map (CommRingCat.ofHom (algebraMap A B)))).IsEquivalence := by
  obtain ⟨n, ψ, hB, hA⟩ := affineUH_frobeniusFactorization A B p h
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let t := Spec.map (CommRingCat.ofHom ψ)
  have hs : s ≫ t = Spec.map (CommRingCat.ofHom (iterateFrobenius B p n)) := by
    rw [← Spec.map_comp]
    exact congrArg (fun φ : B →+* B ↦ Spec.map (CommRingCat.ofHom φ)) hB
  have ht : t ≫ s = Spec.map (CommRingCat.ofHom (iterateFrobenius A p n)) := by
    rw [← Spec.map_comp]
    exact congrArg (fun φ : A →+* A ↦ Spec.map (CommRingCat.ofHom φ)) hA
  exact (CategoryTheory.Equivalence.mk (etaleDirectImage s) (etaleDirectImage t)
    (etaleDirectImageCompIso s t ≪≫ eqToIso (congrArg etaleDirectImage hs) ≪≫
      affineIterateFrobeniusEtaleIso B p n).symm
    (etaleDirectImageCompIso t s ≪≫ eqToIso (congrArg etaleDirectImage ht) ≪≫
      affineIterateFrobeniusEtaleIso A p n)).isEquivalence_functor

/-- Every UH denominator above G_m in the finite-type scheme category induces
an actual equivalence on étale sheaves. Affineness of its source is proved from
the literal universal-homeomorphism condition. -/
theorem multiplicativeGroupUH_etaleDirectImage_isEquivalence
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (Z : FiniteTypeSchemes (Spec (.of k)))
    (s : Z ⟶ multiplicativeGroupFiniteType k) (hs : relativeUH _ s) :
    (etaleDirectImage s.left).IsEquivalence := by
  have : IsAffine (multiplicativeGroupFiniteType k).left :=
    inferInstanceAs (IsAffine (Spec (.of (LaurentPolynomial k))))
  have : IsAffineHom s.left :=
    isAffineHom_of_homeomorph s.left (universalHomeomorphism_homeomorph s.left hs)
  have : IsAffine Z.left := isAffine_of_isAffineHom s.left
  let B := Γ(Z.left, ⊤)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.left.isoSpec.inv ≫ s.left)
  have hUH : universalHomeomorphisms (Spec.map φ) := by
    rw [hφ]
    exact (universalHomeomorphisms.cancel_left_of_respectsIso _ _).mpr hs
  have hsurj : Function.Surjective (PrimeSpectrum.comap φ.hom) :=
    (universalHomeomorphism_homeomorph _ hUH).surjective
  have : Nonempty (PrimeSpectrum B) := ⟨hsurj ⟨⊥, inferInstance⟩ |>.choose⟩
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Algebra k B := (φ.hom.comp (algebraMap k (LaurentPolynomial k))).toAlgebra
  have : CharP B p := (Algebra.charP_iff k B p).mp inferInstance
  let : Algebra (LaurentPolynomial k) B := φ.hom.toAlgebra
  have hsft : LocallyOfFiniteType s.left :=
    (finiteTypeScheme_hom_finiteType (Spec (.of k)) s).1
  have hφft : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have : Algebra.FiniteType (LaurentPolynomial k) B :=
    HasRingHomProperty.Spec_iff.mp hφft
  have H := affineUH_etaleDirectImage_isEquivalence (LaurentPolynomial k) B p hUH
  change (etaleDirectImage (Spec.map φ)).IsEquivalence at H
  rw [hφ] at H
  have : (etaleDirectImage Z.left.isoSpec.inv ⋙ etaleDirectImage s.left).IsEquivalence :=
    Functor.isEquivalence_of_iso (etaleDirectImageCompIso _ _).symm
  exact Functor.isEquivalence_of_comp_left (etaleDirectImage Z.left.isoSpec.inv)
    (etaleDirectImage s.left)

end EtaleCounterexample
