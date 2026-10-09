import EtaleCounterexample.EtalePoints
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Limits.MorphismProperty
import EtaleCounterexample.SmallSourceSite

set_option autoImplicit false

noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u

/-- Actual base change on the small étale sites. -/
abbrev etaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback (@Etale) ⊤ f

instance etaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (etaleBaseChange f) :=
  inferInstanceAs (PreservesFiniteLimits
    (MorphismProperty.Over.pullback (@Etale) ⊤ f))

theorem etaleBaseChange_coverPreserving {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (etaleBaseChange f) := by
  constructor
  intro U R hR
  change R ∈ (MorphismProperty.Over.forget (@Etale) ⊤ Y).restrictedTopology
    (Scheme.etaleTopology.over Y) U at hR
  rw [Functor.mem_restrictedTopology_iff] at hR
  change _ ∈ (MorphismProperty.Over.forget (@Etale) ⊤ X).restrictedTopology
    (Scheme.etaleTopology.over X) _
  rw [Functor.mem_restrictedTopology_iff]
  have h := (GrothendieckTopology.coverPreserving_overPullback
    (J := Scheme.etaleTopology) f).cover_preserve hR
  rw [← Sieve.functorPushforward_comp] at h ⊢
  exact h

instance etaleBaseChange_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  have : RepresentablyFlat (etaleBaseChange f) := flat_of_preservesFiniteLimits _
  exact (Functor.isContinuous_iff_coverPreserving ..).2
    (etaleBaseChange_coverPreserving f)

instance affineEtaleSpec_preservesPullbacks (Y : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (Scheme.AffineEtale.Spec Y) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    (MorphismProperty.CostructuredArrow.toOver (@Etale) Scheme.Spec Y))

/-- The identity affine étale object is terminal over an affine base. -/
def affineEtaleIdentityIsTerminal (R : CommRingCat.{u}) :
    IsTerminal (Scheme.AffineEtale.mk (𝟙 (Spec R))) :=
  IsTerminal.isTerminalOfObj (Scheme.AffineEtale.Spec (Spec R)) _
    (MorphismProperty.Over.mkIdTerminal (@Etale) (Spec R))

instance affineEtale_hasTerminal (R : CommRingCat.{u}) :
    HasTerminal (Spec R).AffineEtale := (affineEtaleIdentityIsTerminal R).hasTerminal

instance affineEtaleSpec_preservesTerminal (R : CommRingCat.{u}) :
    PreservesLimit (Functor.empty.{0} (Spec R).AffineEtale)
      (Scheme.AffineEtale.Spec (Spec R)) :=
  preservesLimit_of_preserves_limit_cone (affineEtaleIdentityIsTerminal R)
    ((isLimitMapConeEmptyConeEquiv _ _).symm
      (MorphismProperty.Over.mkIdTerminal (@Etale) (Spec R)))

instance affineEtale_hasFiniteLimits (R : CommRingCat.{u}) :
    HasFiniteLimits (Spec R).AffineEtale := hasFiniteLimits_of_hasTerminal_and_pullbacks

instance affineEtaleSpec_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (Scheme.AffineEtale.Spec (Spec R)) := by
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (Scheme.AffineEtale.Spec (Spec R))
  exact
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

abbrev SmallAffineEtale (Y : Scheme.{u}) := SmallModel.{u} Y.AffineEtale

abbrev smallAffineEtaleTopology (Y : Scheme.{u}) : GrothendieckTopology (SmallAffineEtale Y) :=
  (equivSmallModel.{u} Y.AffineEtale).inverse.inducedTopology
    (Scheme.AffineEtale.topology Y)

def smallAffineEtaleInclusion (Y : Scheme.{u}) : SmallAffineEtale Y ⥤ Y.Etale :=
  (equivSmallModel.{u} Y.AffineEtale).inverse ⋙ Scheme.AffineEtale.Spec Y

instance smallAffineEtaleInclusion_continuous (Y : Scheme.{u}) :
    (smallAffineEtaleInclusion Y).IsContinuous (smallAffineEtaleTopology Y)
      Y.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ (Scheme.AffineEtale.topology Y) _

def smallAffineRestriction (Y : Scheme.{u}) :
    EtaleTopos Y ⥤ Sheaf (smallAffineEtaleTopology Y) (Type u) :=
  (smallAffineEtaleInclusion Y).sheafPushforwardContinuous _ _ _

instance smallAffineRestriction_isEquivalence (Y : Scheme.{u}) :
    (smallAffineRestriction Y).IsEquivalence := by
  change ((Scheme.AffineEtale.Spec Y).sheafPushforwardContinuous (Type u)
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology ⋙
    (equivSmallModel.{u} Y.AffineEtale).inverse.sheafPushforwardContinuous (Type u)
      (smallAffineEtaleTopology Y) (Scheme.AffineEtale.topology Y)).IsEquivalence
  infer_instance

instance smallAffineEtaleInclusion_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (smallAffineEtaleInclusion (Spec R)) :=
  inferInstanceAs (PreservesFiniteLimits
    ((equivSmallModel.{u} (Spec R).AffineEtale).inverse ⋙ Scheme.AffineEtale.Spec (Spec R)))

def smallAffineBaseChange {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    SmallAffineEtale (Spec R) ⥤ X.Etale :=
  smallAffineEtaleInclusion (Spec R) ⋙ etaleBaseChange f

instance smallAffineBaseChange_continuous {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) :
    (smallAffineBaseChange f).IsContinuous (smallAffineEtaleTopology (Spec R))
      X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ (Spec R).smallEtaleTopology _

instance smallAffineBaseChange_flat {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) : RepresentablyFlat (smallAffineBaseChange f) := by
  have : HasFiniteLimits (SmallAffineEtale (Spec R)) :=
    hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits
      (equivSmallModel.{u} (Spec R).AffineEtale).inverse
  have : PreservesFiniteLimits (smallAffineBaseChange f) :=
    inferInstanceAs (PreservesFiniteLimits
      (smallAffineEtaleInclusion (Spec R) ⋙ etaleBaseChange f))
  exact flat_of_preservesFiniteLimits _

/-- Direct image is literally evaluation on scheme base changes. -/
def etaleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) : EtaleTopos X ⥤ EtaleTopos Y :=
  (etaleBaseChange f).sheafPushforwardContinuous _ _ _

/-- The left adjoint, constructed using the small affine étale subsite of the base. -/
def affineBaseEtaleInverseImage {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    EtaleTopos (Spec R) ⥤ EtaleTopos X :=
  smallAffineRestriction (Spec R) ⋙ (smallAffineBaseChange f).sheafPullback _ _ _

def affineBaseEtaleAdjunction {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    affineBaseEtaleInverseImage f ⊣ etaleDirectImage f :=
  ((smallAffineRestriction (Spec R)).asEquivalence.toAdjunction.comp
    ((smallAffineBaseChange f).sheafAdjunctionContinuous (Type u) _ _)).ofNatIsoRight
      ((Functor.associator (etaleDirectImage f) (smallAffineRestriction (Spec R))
        (smallAffineRestriction (Spec R)).asEquivalence.inverse) ≪≫
      isoWhiskerLeft (etaleDirectImage f)
        (smallAffineRestriction (Spec R)).asEquivalence.unitIso.symm ≪≫
      (etaleDirectImage f).rightUnitor)

/-- The actual geometric morphism on `Type u`-valued small étale sheaves for
any scheme morphism with affine target. -/
def affineBaseEtaleMorphism {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    GeometricMorphism (EtaleTopos X) (EtaleTopos (Spec R)) where
  inverseImage := affineBaseEtaleInverseImage f
  directImage := etaleDirectImage f
  adjunction := affineBaseEtaleAdjunction f
  leftExact := inferInstanceAs (PreservesFiniteLimits
    (smallAffineRestriction (Spec R) ⋙ (smallAffineBaseChange f).sheafPullback _ _ _))

end EtaleCounterexample
