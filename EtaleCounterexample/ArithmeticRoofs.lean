import EtaleCounterexample.Counterexamples

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
variable (p : ℕ) [Fact p.Prime]

/-- Any arithmetic roof above G_m/F_p already has a genuine F_p-structure on
its source, obtained by composing its denominator with the G_m structure map. -/
def arithmeticRoofSource (Z : FiniteTypeSchemes (Spec (.of ℤ)))
    (s : Z ⟶ arithmeticMultiplicativeGroup p) : FiniteTypeSchemes (Spec (.of (ZMod p))) :=
  MorphismProperty.Over.mk ⊤ (s.left ≫ multiplicativeGroupStructure (ZMod p))
    (finiteType.comp_mem _ _ (finiteTypeScheme_hom_finiteType _ s)
      (multiplicativeGroupFiniteType (ZMod p)).prop)

def arithmeticRoofSourceIso (Z : FiniteTypeSchemes (Spec (.of ℤ)))
    (s : Z ⟶ arithmeticMultiplicativeGroup p) :
    (inclusion (primeBase p)).obj (arithmeticRoofSource p Z s) ≅ Z :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change (𝟙 Z.left) ≫ Z.hom = (s.left ≫ multiplicativeGroupStructure (ZMod p)) ≫ primeBase p
    rw [Category.id_comp, Category.assoc]
    exact s.w.symm)

def arithmeticRoofDenominator (Z : FiniteTypeSchemes (Spec (.of ℤ)))
    (s : Z ⟶ arithmeticMultiplicativeGroup p) :
    arithmeticRoofSource p Z s ⟶ multiplicativeGroupFiniteType (ZMod p) :=
  MorphismProperty.Over.homMk s.left rfl trivial

def arithmeticRoofNumerator (Z : FiniteTypeSchemes (Spec (.of ℤ)))
    (s f : Z ⟶ arithmeticMultiplicativeGroup p) :
    arithmeticRoofSource p Z s ⟶ multiplicativeGroupFiniteType (ZMod p) :=
  MorphismProperty.Over.homMk f.left (by
    apply (cancel_mono (primeBase p)).mp
    simp only [Category.assoc]
    exact f.w.trans s.w.symm) trivial

theorem arithmeticRoofDenominator_over (Z : FiniteTypeSchemes (Spec (.of ℤ)))
    (s : Z ⟶ arithmeticMultiplicativeGroup p) :
    (inclusion (primeBase p)).map (arithmeticRoofDenominator p Z s) =
      (arithmeticRoofSourceIso p Z s).hom ≫ s := by
  ext; simp [arithmeticRoofSourceIso, arithmeticRoofDenominator]

theorem arithmeticRoofNumerator_over (Z : FiniteTypeSchemes (Spec (.of ℤ)))
    (s f : Z ⟶ arithmeticMultiplicativeGroup p) :
    (inclusion (primeBase p)).map (arithmeticRoofNumerator p Z s f) =
      (arithmeticRoofSourceIso p Z s).hom ≫ f := by
  ext; simp [arithmeticRoofSourceIso, arithmeticRoofNumerator]

/-- All arithmetic roof representatives, including those extracted from
arbitrary mixed-characteristic zigzags, correspond to actual finite-field roofs. -/
def arithmeticRoofAsFiniteFieldRoof
    (a : End ((relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p)))
    (Z : FiniteTypeSchemes (Spec (.of ℤ))) (s f : Z ⟶ arithmeticMultiplicativeGroup p)
    (hs : relativeUH _ s) (ha : (relativeUH _).Q.map s ≫ a = (relativeUH _).Q.map f) :
    MultiplicativeGroupLocalizedRoof (ZMod p) ((primeFieldFiniteTypeHomEquiv p _ _).symm a) where
  source := arithmeticRoofSource p Z s
  denominator := arithmeticRoofDenominator p Z s
  numerator := arithmeticRoofNumerator p Z s f
  isUH := hs
  represents := by
    apply (primeFieldFiniteTypeHomEquiv p _ _).injective
    rw [primeFieldFiniteTypeHomEquiv_comp, Equiv.apply_symm_apply,
      primeFieldFiniteTypeHomEquiv_map, primeFieldFiniteTypeHomEquiv_map,
      arithmeticRoofDenominator_over, arithmeticRoofNumerator_over]
    simp only [Functor.map_comp, Category.assoc]
    rw [ha]

/-- The realization of every arithmetic scheme roof agrees with the canonical
arithmetic localized-endomorphism comparison in actual relative isomorphism
classes. The direct images are those of the original denominator and numerator. -/
theorem arithmeticEtaleEndomorphismHom_roof
    (a : End ((relativeUH (Spec (.of ℤ))).Q.obj (arithmeticMultiplicativeGroup p)))
    (Z : FiniteTypeSchemes (Spec (.of ℤ))) (s f : Z ⟶ arithmeticMultiplicativeGroup p)
    (hs : relativeUH _ s) (ha : (relativeUH _).Q.map s ≫ a = (relativeUH _).Q.map f) :
    arithmeticEtaleEndomorphismHom p a = relativeEndomorphismClass
      (((arithmeticRoofAsFiniteFieldRoof p a Z s f hs ha).etaleMorphism (ZMod p) p).postcompose
        (etaleDirectImage (primeBase p))) := by
  apply Quotient.sound
  exact ⟨_, (localizedEtaleEndomorphism_independent (ZMod p) p
    (arithmeticRoofAsFiniteFieldRoof p a Z s f hs ha)).choose_spec.postcompose
      (etaleDirectImage (primeBase p))⟩

end EtaleCounterexample
