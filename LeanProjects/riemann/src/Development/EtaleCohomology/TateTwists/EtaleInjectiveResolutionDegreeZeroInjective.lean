import Development.EtaleCohomology.TateTwists.EtaleTwistExtendsThroughMonoToResolutionZero

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

theorem etale_injective_resolution_degree_zero_injective (q : ℕ) (F : Shv (ZMod q)) : Injective ((res _ F).X 0) := by
  unfold res
  exact inferInstance

theorem etale_twist_extends_through_mono_to_resolution_holds : EtaleTwistExtendsThroughMonoToResolutionZero := by
  intro q _ M j hj
  have := etale_injective_resolution_degree_zero_injective q (tw q 1)
  exact ⟨Injective.factorThru (resι _ (tw q 1)) j, Injective.comp_factorThru _ _⟩

end LateralTheory.EtaleFoundations
