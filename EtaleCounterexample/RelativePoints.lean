import EtaleCounterexample.FrobeniusMate
import EtaleCounterexample.MultiplicativeGroup

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

def etalePointCompIsoOfEq (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    {ω : Spec (.of Ω) ⟶ Y} (h : s ≫ f = ω) :
    (etalePoint s).directImage ⋙ etaleDirectImage f ≅ (etalePoint ω).directImage :=
  etalePointCompIso f s ≪≫ eqToIso (congrArg (fun ω ↦ (etalePoint ω).directImage) h)

/-- The comparison to a fixed base point includes the actual pullback comparison. -/
def relativeEtalePoint (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    {ω : Spec (.of Ω) ⟶ Y} (h : s ≫ f = ω) :
    RelativeMorphism (etalePoint ω).directImage (etaleDirectImage f) where
  geometric := etalePoint s
  comparison := etalePointCompIsoOfEq f s h

/-- Postcompose a relative morphism with the identity twist of its target.
Functor identity unitors are absorbed definitionally. -/
def twistRelativeEtalePoint (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    {ω : Spec (.of Ω) ⟶ Y} (h : s ≫ f = ω)
    (η : 𝟭 (EtaleTopos Y) ≅ 𝟭 (EtaleTopos Y)) :
    RelativeMorphism (etalePoint ω).directImage (etaleDirectImage f) where
  geometric := etalePoint s
  comparison := isoWhiskerLeft ((etalePoint s).directImage ⋙ etaleDirectImage f) η ≪≫
    etalePointCompIsoOfEq f s h

/-- Base naturality after identifying the two structural scheme points. -/
theorem etalePointRightMate_fixedBase (e : Spec (.of Ω) ≅ Spec (.of Ω))
    (f : X ⟶ Y) {s t : Spec (.of Ω) ⟶ X} (h : e.hom ≫ s = t)
    {ω ω' : Spec (.of Ω) ⟶ Y} (hs : s ≫ f = ω) (ht : t ≫ f = ω')
    (he : e.hom ≫ ω = ω') (M : Type u) :
    (etaleDirectImage f).map ((etalePointRightMateOfEq e h).hom.app M) ≫
        (etalePointCompIsoOfEq f s hs).hom.app M =
      (etalePointCompIsoOfEq f t ht).hom.app M ≫
        (etalePointRightMateOfEq e he).hom.app M := by
  subst ω
  subst ω'
  simpa [etalePointCompIsoOfEq] using etalePointRightMate_base e f h M

/-- A proved base-mate equation yields the actual relative point triangle.
This general lemma has an explicit base-equation hypothesis; it is discharged
by the Frobenius theorem below. -/
theorem relativePointAction_of_baseEquation
    (e : Spec (.of Ω) ≅ Spec (.of Ω)) (f : X ⟶ Y)
    (s : Spec (.of Ω) ⟶ X) {ω : Spec (.of Ω) ⟶ Y}
    (hs : s ≫ f = ω) (he : e.hom ≫ ω = ω)
    (η : 𝟭 (EtaleTopos Y) ≅ 𝟭 (EtaleTopos Y))
    (hη : ∀ M : Type u, (etalePointRightMateOfEq e he).hom.app M =
      η.hom.app ((etalePoint ω).directImage.obj M)) :
    RelativeCompatible (twistRelativeEtalePoint f s hs η.symm)
      (relativeEtalePoint f (e.hom ≫ s)
        (show (e.hom ≫ s) ≫ f = ω by rw [Category.assoc, hs, he]))
      (etalePointRightMateOfEq e rfl).symm := by
  intro M
  let ht : (e.hom ≫ s) ≫ f = ω := by rw [Category.assoc, hs, he]
  have H := etalePointRightMate_fixedBase e f rfl hs ht he M
  rw [hη] at H
  exact inverseMate_twistTriangle (etaleDirectImage f)
    ((etalePointRightMateOfEq e rfl).app M)
    ((etalePointCompIsoOfEq f s hs).app M)
    ((etalePointCompIsoOfEq f (e.hom ≫ s) ht).app M) η H

variable (k : Type u) [Field k] [Fintype k] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω]

/-- The actual identity twist whose comparison is inverse arithmetic Frobenius. -/
def arithmeticFrobeniusTwist (f : X ⟶ Spec (.of k)) :
    RelativeMorphism (etaleDirectImage f) (etaleDirectImage f) :=
  identityTwist (etaleDirectImage f) (finiteFieldFrobeniusToposIso k).symm

/-- An actual relative isomorphism with the proposed sign: twisting by
`η_F⁻¹` takes a relative geometric point `s` to `Spec(F) ≫ s`.
The displayed isomorphism is the inverse of the explicitly constructed mate. -/
theorem arithmeticFrobenius_relativePointAction
    (f : X ⟶ Spec (.of k)) (s : Spec (.of Ω) ⟶ X)
    (hs : s ≫ f = fieldGeometricPoint k Ω) :
    RelativeCompatible
      (twistRelativeEtalePoint f s hs (finiteFieldFrobeniusToposIso k).symm)
      (relativeEtalePoint f ((arithmeticFrobeniusSpec k Ω).hom ≫ s)
        (show ((arithmeticFrobeniusSpec k Ω).hom ≫ s) ≫ f =
            fieldGeometricPoint k Ω by
          rw [Category.assoc, hs, arithmeticFrobeniusSpec_over]))
      (etalePointRightMateOfEq (arithmeticFrobeniusSpec k Ω) rfl).symm :=
  relativePointAction_of_baseEquation (arithmeticFrobeniusSpec k Ω) f s hs
    (arithmeticFrobeniusSpec_over k Ω) (finiteFieldFrobeniusToposIso k)
    (frobeniusPointMate_eq_toposIso k Ω)

end EtaleCounterexample
