import EtaleCounterexample.UniversalHomeomorphisms
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Etale

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace EtaleCounterexample
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The diagonal of an étale radicial morphism is a surjective open immersion,
so the morphism is a monomorphism. -/
theorem etale_mono_of_universallyInjective [Etale f] [UniversallyInjective f] :
    Mono f := by
  have : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  have : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  exact (pullback.isIso_diagonal_iff f).mp inferInstance

/-- An actual étale universal homeomorphism of schemes is an isomorphism.
No invariance statement about topoi is used in this proof. -/
theorem etale_universalHomeomorphism_isIso [Etale f]
    (hf : universalHomeomorphisms f) : IsIso f := by
  have : UniversallyInjective f := universalHomeomorphism_universallyInjective f hf
  have : Mono f := etale_mono_of_universallyInjective f
  have : Surjective f := ⟨(universalHomeomorphism_homeomorph f hf).surjective⟩
  have : IsIntegralHom f := universalHomeomorphism_integral f hf
  exact Flat.isIso_of_surjective_of_mono f

/-- The surjective radicial form needs no separate integrality hypothesis. -/
theorem etale_surjective_radicial_isIso [Etale f] [Surjective f]
    [UniversallyInjective f] : IsIso f := by
  have : Mono f := etale_mono_of_universallyInjective f
  have : IsOpenImmersion f := IsOpenImmersion.of_flat_of_mono f
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

end EtaleCounterexample
