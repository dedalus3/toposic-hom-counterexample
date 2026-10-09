import EtaleCounterexample.Localization
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-!
Actual finite-type schemes localized at universal homeomorphisms.
Universal homeomorphism is defined literally by the topological condition on
every scheme base change. No assertion of étale invariance is built into it.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace EtaleCounterexample
universe u

/-- Finite type means locally finite type and quasi-compact. -/
abbrev finiteType : MorphismProperty Scheme.{u} :=
  (@LocallyOfFiniteType) ⊓ (@QuasiCompact)

/-- All schemes in `Scheme.{u}` finite type over `S`; all `S`-morphisms. -/
abbrev FiniteTypeSchemes (S : Scheme.{u}) :=
  MorphismProperty.Over finiteType ⊤ S

/-- The underlying scheme functor. -/
def underlying (S : Scheme.{u}) : FiniteTypeSchemes S ⥤ Scheme.{u} :=
  MorphismProperty.Over.forget _ _ S ⋙ CategoryTheory.Over.forget S

/-- Every base change is a homeomorphism on underlying topological spaces. -/
def universalHomeomorphisms : MorphismProperty Scheme.{u} :=
  (topologically IsHomeomorph).universally

instance : universalHomeomorphisms.{u}.IsStableUnderBaseChange :=
  inferInstanceAs (topologically IsHomeomorph).universally.IsStableUnderBaseChange

/-- Universal homeomorphisms in the finite-type over-category. -/
def relativeUH (S : Scheme.{u}) : MorphismProperty (FiniteTypeSchemes S) :=
  universalHomeomorphisms.inverseImage (underlying S)

/-- Gabriel–Zisman localization; morphisms include arbitrary finite zigzags. -/
abbrev LocalizedSchemes (S : Scheme.{u}) := (relativeUH S).Localization

variable {S T : Scheme.{u}} (i : S ⟶ T) [LocallyOfFiniteType i] [QuasiCompact i]

abbrev inclusion : FiniteTypeSchemes S ⥤ FiniteTypeSchemes T :=
  MorphismProperty.Over.map ⊤ (show finiteType i from ⟨inferInstance, inferInstance⟩)

abbrev restriction : FiniteTypeSchemes T ⥤ FiniteTypeSchemes S :=
  MorphismProperty.Over.pullback finiteType ⊤ i

/-- The ordinary change-of-base adjunction, on the actual finite-type categories. -/
def inclusionRestrictionAdjunction : inclusion i ⊣ restriction i :=
  MorphismProperty.Over.mapPullbackAdj finiteType ⊤ i ⟨inferInstance, inferInstance⟩ trivial

/-- Postcomposition along a monomorphism is fully faithful on these categories. -/
def inclusionFullyFaithful [Mono i] : (inclusion i).FullyFaithful where
  preimage {X Y} f := MorphismProperty.Over.homMk f.left (by
    apply (cancel_mono i).mp
    simpa using f.w) trivial
  map_preimage _ := by ext; rfl
  preimage_map _ := by ext; rfl

def inclusionLocalizer : LocalizerMorphism (relativeUH S) (relativeUH T) where
  functor := inclusion i
  map _ _ _ h := h

/-- Base change preserves universal homeomorphisms, on arrows as well as objects. -/
def restrictionLocalizer : LocalizerMorphism (relativeUH T) (relativeUH S) where
  functor := restriction i
  map {X Y} f h := by
    exact universalHomeomorphisms.pullbackLift_fst_snd i f.w.symm h

def localizedInclusion : LocalizedSchemes S ⥤ LocalizedSchemes T :=
  (inclusionLocalizer i).localizedFunctor (relativeUH S).Q (relativeUH T).Q

def localizedRestriction : LocalizedSchemes T ⥤ LocalizedSchemes S :=
  (restrictionLocalizer i).localizedFunctor (relativeUH T).Q (relativeUH S).Q

/-- This full-faithfulness statement covers arbitrary intermediate `T`-schemes. -/
def localizedInclusionFullyFaithful [Mono i] : (localizedInclusion i).FullyFaithful := by
  letI := (inclusionFullyFaithful i).full
  letI := (inclusionFullyFaithful i).faithful
  letI : CatCommSq (inclusion i) (relativeUH S).Q (relativeUH T).Q
      (localizedInclusion i) := (inclusionLocalizer i).catCommSq _ _
  letI : CatCommSq (restriction i) (relativeUH T).Q (relativeUH S).Q
      (localizedRestriction i) := (restrictionLocalizer i).catCommSq _ _
  exact localizedFullyFaithful (inclusionRestrictionAdjunction i)
    (relativeUH S).Q (relativeUH S) (relativeUH T).Q (relativeUH T)
    (localizedInclusion i) (localizedRestriction i)

/-- The hom-set comparison for any finite-type monomorphism of base schemes. -/
def localizedHomEquiv [Mono i] (X Y : LocalizedSchemes S) :
    (X ⟶ Y) ≃ ((localizedInclusion i).obj X ⟶ (localizedInclusion i).obj Y) :=
  (localizedInclusionFullyFaithful i).homEquiv

/-- The actual closed immersion `Spec (ZMod p) → Spec ℤ`. -/
def primeBase (p : ℕ) : Spec (.of (ZMod p)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p)))

instance primeBase_isClosedImmersion (p : ℕ) : IsClosedImmersion (primeBase p) :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.intCast_surjective)

/-- The requested algebraic comparison over the prime field (indeed valid for
all `ZMod p`). This says nothing by itself about the associated étale morphisms.
Mixed-characteristic intermediate schemes in the right-hand localization are
unrestricted. -/
def primeFieldLocalizedHomEquiv (p : ℕ)
    (X Y : LocalizedSchemes (Spec (.of (ZMod p)))) :
    (X ⟶ Y) ≃
      ((localizedInclusion (primeBase p)).obj X ⟶
       (localizedInclusion (primeBase p)).obj Y) :=
  localizedHomEquiv (primeBase p) X Y

/-- The same comparison stated on the images of actual finite-type schemes,
with the canonical change-of-base comparison isomorphisms applied explicitly. -/
def primeFieldFiniteTypeHomEquiv (p : ℕ)
    (X Y : FiniteTypeSchemes (Spec (.of (ZMod p)))) :
    ((relativeUH (Spec (.of (ZMod p)))).Q.obj X ⟶
     (relativeUH (Spec (.of (ZMod p)))).Q.obj Y) ≃
    ((relativeUH (Spec (.of ℤ))).Q.obj ((inclusion (primeBase p)).obj X) ⟶
     (relativeUH (Spec (.of ℤ))).Q.obj ((inclusion (primeBase p)).obj Y)) :=
  (primeFieldLocalizedHomEquiv p _ _).trans
    (Iso.homCongr
      (((inclusionLocalizer (primeBase p)).catCommSq _ _).iso.app X).symm
      (((inclusionLocalizer (primeBase p)).catCommSq _ _).iso.app Y).symm)

end EtaleCounterexample
