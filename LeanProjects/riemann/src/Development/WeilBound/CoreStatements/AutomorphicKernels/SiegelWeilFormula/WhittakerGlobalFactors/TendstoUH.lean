import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_UH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (bs : Module.Basis (Fin d) F E) (n : ℕ)
    (ν : Measure (HermR (AF F) σ n)) (f : HermR (AF F) σ n → ℂ) (hf : Integrable f ν) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ∫ b in UH σ bs n S, f b ∂ν) atTop (nhds (∫ b, f b ∂ν)) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have he : ∀ S, ∫ b in UH σ bs n S, f b ∂ν = ∫ b, (UH σ bs n S).indicator f b ∂ν := fun S =>
    (integral_indicator (measurableSet_UH σ hCM bs n S)).symm
  simp_rw [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall fun S => hf.aestronglyMeasurable.indicator (measurableSet_UH σ hCM bs n S)
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_
    by_cases h : y ∈ UH σ bs n S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ bs v n}.Finite :=
      Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_latH σ bs y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : y ∈ UH σ bs n S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [Set.indicator_of_mem hmem]

end PositivityTheory.SiegelWeilFormula.GFac

end
