import EtaleCounterexample.EtaleComposition
import EtaleCounterexample.RelativeIsoCalculus

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
namespace EtaleCounterexample
universe u

def etaleDirectImageCompIsoOfEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {fg : X ⟶ Z} (hfg : f ≫ g = fg) :
    etaleDirectImage f ⋙ etaleDirectImage g ≅ etaleDirectImage fg :=
  etaleDirectImageCompIso f g ≪≫ eqToIso (congrArg etaleDirectImage hfg)

theorem etaleDirectImageCompIsoOfEq_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {fg : X ⟶ Z} (hfg : f ≫ g = fg)
    (M : EtaleTopos X) (U : Z.Etale) :
    ((etaleDirectImageCompIsoOfEq f g hfg).hom.app M).hom.app (op U) =
      M.obj.map (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        f g fg hfg.symm).hom.app U).op) := by
  subst fg
  rfl

/-- Coherence of the actual étale direct-image comparisons, with all scheme
equalities explicit. The proof is equality of pullback maps on the actual site. -/
theorem etaleDirectImage_composition_coherence {X Y Z S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ S)
    (fg : X ⟶ Z) (π : X ⟶ S) (ρ : Y ⟶ S)
    (hfg : f ≫ g = fg) (hρ : g ≫ h = ρ) (hfρ : f ≫ ρ = π) (hfgh : fg ≫ h = π)
    (M : EtaleTopos X) :
    (etaleDirectImage h).map ((etaleDirectImageCompIsoOfEq f g hfg).hom.app M) ≫
      (etaleDirectImageCompIsoOfEq fg h hfgh).hom.app M =
    (etaleDirectImageCompIsoOfEq g h hρ).hom.app ((etaleDirectImage f).obj M) ≫
      (etaleDirectImageCompIsoOfEq f ρ hfρ).hom.app M := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  obtain ⟨U⟩ := U
  change ((etaleDirectImageCompIsoOfEq f g hfg).hom.app M).hom.app
        (op ((etaleBaseChange h).obj U)) ≫
      ((etaleDirectImageCompIsoOfEq fg h hfgh).hom.app M).hom.app (op U) =
    ((etaleDirectImageCompIsoOfEq g h hρ).hom.app ((etaleDirectImage f).obj M)).hom.app (op U) ≫
      ((etaleDirectImageCompIsoOfEq f ρ hfρ).hom.app M).hom.app (op U)
  simp only [etaleDirectImageCompIsoOfEq_app]
  change M.obj.map _ ≫ M.obj.map _ = M.obj.map _ ≫ M.obj.map _
  rw [← M.obj.map_comp, ← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullbackComp, etaleBaseChange, ← hfg]
    · simp [MorphismProperty.Over.pullbackComp, etaleBaseChange, ← hfg]
  · simp [MorphismProperty.Over.pullbackComp, etaleBaseChange, ← hfg]

end EtaleCounterexample
