import EtaleCounterexample.SchemeFrobenius
import EtaleCounterexample.EtaleRadicial

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) [Fact p.Prime]
  (h : (p : Γ(Y, ⊤)) = 0)

/-- The actual relative Frobenius, with the same pullback ordering as the
small-étale-site base-change functor. -/
def relativeFrobenius : X ⟶ pullback f (schemeFrobenius Y p h) :=
  pullback.lift (schemeFrobenius X p (prime_eq_zero_of_hom f p h)) f
    (schemeFrobenius_naturality f p _ h)

@[reassoc (attr := simp)] theorem relativeFrobenius_fst :
    relativeFrobenius f p h ≫ pullback.fst f (schemeFrobenius Y p h) =
      schemeFrobenius X p (prime_eq_zero_of_hom f p h) := pullback.lift_fst ..

@[reassoc (attr := simp)] theorem relativeFrobenius_snd :
    relativeFrobenius f p h ≫ pullback.snd f (schemeFrobenius Y p h) = f :=
  pullback.lift_snd ..

instance relativeFrobenius_surjective : Surjective (relativeFrobenius f p h) := by
  have hF := schemeFrobenius_universallyInjective Y p h
  have : UniversallyInjective (pullback.fst f (schemeFrobenius Y p h)) :=
    MorphismProperty.pullback_fst _ _ hF
  constructor
  intro x
  refine ⟨pullback.fst f (schemeFrobenius Y p h) x, ?_⟩
  apply (pullback.fst f (schemeFrobenius Y p h)).injective
  rw [← Scheme.Hom.comp_apply, relativeFrobenius_fst, schemeFrobenius_apply]

instance relativeFrobenius_universallyInjective :
    UniversallyInjective (relativeFrobenius f p h) := by
  apply ((tfae_universallyInjective (relativeFrobenius f p h)).out 1 2).mpr
  intro K _ a b hab
  have H := schemeFrobenius_universallyInjective X p (prime_eq_zero_of_hom f p h)
  have Hfield := ((tfae_universallyInjective
    (schemeFrobenius X p (prime_eq_zero_of_hom f p h))).out 1 2).mp H
  apply Hfield K
  have H' := congrArg (fun t ↦ t ≫ pullback.fst f (schemeFrobenius Y p h)) hab
  simpa using H'

instance relativeFrobenius_etale [Etale f] : Etale (relativeFrobenius f p h) := by
  have : Etale (relativeFrobenius f p h ≫ pullback.snd f (schemeFrobenius Y p h)) := by
    rw [relativeFrobenius_snd]; infer_instance
  exact Etale.of_comp _ (pullback.snd f (schemeFrobenius Y p h))

/-- Relative Frobenius of every actual étale scheme is an isomorphism. -/
instance relativeFrobenius_isIso [Etale f] : IsIso (relativeFrobenius f p h) :=
  etale_surjective_radicial_isIso _

/-- Relative Frobenius as a natural isomorphism on the actual small étale site. -/
def etaleRelativeFrobeniusIso : 𝟭 Y.Etale ≅ etaleBaseChange (schemeFrobenius Y p h) :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.Over.isoMk (asIso (relativeFrobenius U.hom p h))
      (relativeFrobenius_snd U.hom p h)) (by
    intro U V a
    apply MorphismProperty.Over.Hom.ext
    change a.left ≫ relativeFrobenius V.hom p h = relativeFrobenius U.hom p h ≫
      pullback.lift (pullback.fst U.hom (schemeFrobenius Y p h) ≫ a.left)
        (pullback.snd U.hom (schemeFrobenius Y p h)) _
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeFrobenius_fst, pullback.lift_fst]
      rw [← Category.assoc]
      erw [relativeFrobenius_fst]
      exact (schemeFrobenius_naturality a.left p _ _).symm
    · simp [CategoryTheory.Over.w])

/-- Actual direct-image invariance under absolute Frobenius. -/
def schemeFrobeniusEtaleDirectImageIso :
    etaleDirectImage (schemeFrobenius Y p h) ≅ 𝟭 (EtaleTopos Y) := by
  letI := etaleBaseChange_continuous (schemeFrobenius Y p h)
  exact Functor.sheafPushforwardContinuousId' (etaleRelativeFrobeniusIso p h).symm
    (Type u) Y.smallEtaleTopology

end EtaleCounterexample
