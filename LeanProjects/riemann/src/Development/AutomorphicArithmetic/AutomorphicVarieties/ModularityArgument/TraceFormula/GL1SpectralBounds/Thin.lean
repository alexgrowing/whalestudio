import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.SecondFromFirstStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.LyingOverPrimes.InertThin
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.PrimeNonSummability.PrimeSumConvergesAndDiverges

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.GOne.thin :
    Thin := by
  intro E _ _ _
  have hs : Summable fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} =>
      ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹ := PositivityTheory.Rg.BcB.Desc.inertThin_holds E
  refine ⟨hs, fun hfin => ?_⟩
  apply PositivityTheory.RgJS.PrimeSumConvergence.not_summable_all (E := E)
  have hf : Summable fun w : {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w} =>
      ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹ :=
    hfin.summable (fun w : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹)
  exact (summable_subtype_and_compl (f := fun w : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹)
    (s := {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w})).1 ⟨hf, hs⟩
