import EtaleCounterexample.SchemeLocalization

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace EtaleCounterexample
variable (p : ℕ)

theorem primeFieldFiniteTypeHomEquiv_comp
    {X Y Z : FiniteTypeSchemes (Spec (.of (ZMod p)))}
    (a : (relativeUH _).Q.obj X ⟶ (relativeUH _).Q.obj Y)
    (b : (relativeUH _).Q.obj Y ⟶ (relativeUH _).Q.obj Z) :
    primeFieldFiniteTypeHomEquiv p X Z (a ≫ b) =
      primeFieldFiniteTypeHomEquiv p X Y a ≫ primeFieldFiniteTypeHomEquiv p Y Z b := by
  simp [primeFieldFiniteTypeHomEquiv, primeFieldLocalizedHomEquiv, localizedHomEquiv,
    Functor.FullyFaithful.homEquiv, Iso.homCongr, Category.assoc]

theorem primeFieldFiniteTypeHomEquiv_id
    (X : FiniteTypeSchemes (Spec (.of (ZMod p)))) :
    primeFieldFiniteTypeHomEquiv p X X (𝟙 _) = 𝟙 _ := by
  simp [primeFieldFiniteTypeHomEquiv, primeFieldLocalizedHomEquiv, localizedHomEquiv,
    Functor.FullyFaithful.homEquiv, Iso.homCongr, inclusionLocalizer]

theorem primeFieldFiniteTypeHomEquiv_map
    {X Y : FiniteTypeSchemes (Spec (.of (ZMod p)))} (f : X ⟶ Y) :
    primeFieldFiniteTypeHomEquiv p X Y ((relativeUH _).Q.map f) =
      (relativeUH _).Q.map ((inclusion (primeBase p)).map f) := by
  change (((inclusionLocalizer (primeBase p)).catCommSq _ _).iso.app X).hom ≫
      (localizedInclusion (primeBase p)).map ((relativeUH _).Q.map f) ≫
      (((inclusionLocalizer (primeBase p)).catCommSq _ _).iso.app Y).inv = _
  have H := (((inclusionLocalizer (primeBase p)).catCommSq
    (relativeUH (Spec (.of (ZMod p)))).Q (relativeUH (Spec (.of ℤ))).Q).iso).hom.naturality f
  dsimp only [Functor.comp_map] at H
  erw [← Category.assoc, ← H]
  simp [inclusionLocalizer]

theorem primeFieldFiniteTypeHomEquiv_symm_comp
    {X Y Z : FiniteTypeSchemes (Spec (.of (ZMod p)))}
    (a : (relativeUH _).Q.obj ((inclusion (primeBase p)).obj X) ⟶
      (relativeUH _).Q.obj ((inclusion (primeBase p)).obj Y))
    (b : (relativeUH _).Q.obj ((inclusion (primeBase p)).obj Y) ⟶
      (relativeUH _).Q.obj ((inclusion (primeBase p)).obj Z)) :
    (primeFieldFiniteTypeHomEquiv p X Z).symm (a ≫ b) =
      (primeFieldFiniteTypeHomEquiv p X Y).symm a ≫
        (primeFieldFiniteTypeHomEquiv p Y Z).symm b := by
  apply (primeFieldFiniteTypeHomEquiv p X Z).injective
  rw [Equiv.apply_symm_apply, primeFieldFiniteTypeHomEquiv_comp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end EtaleCounterexample
