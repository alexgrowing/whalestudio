import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.PBTied
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AnnDrop

theorem UpperTheory.Gal.crystallineComparison.Br.annModel :
    UpperTheory.Gal.crystallineComparison.Br.AnnModel := by
  intro hF l _ P AI hT K _ _ f hf hc ϖ hϖ M hM n j T hr hP A hA V₀ _ _ i ρ hρ T₀ hT₀
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨B, e, heσ, heφ, hinj⟩ := UpperTheory.Gal.crystallineComparison.Br.pBTied l P AI hT K
  obtain ⟨N, hN⟩ := hF l K.1 f hf hc ϖ hϖ M hM n j T hr hP A hA B
  exact UpperTheory.Gal.crystallineComparison.Br.annDrop ℚ_[l] _ _ _ (UpperTheory.Gal.crystallineComparison.σCr P K) P.φB B.σ B.φ e heσ heφ hinj
    (M.V j) V₀ i (fun g => M.act j g) ρ hρ f (l ^ f) n N A T₀ hT₀ hN
