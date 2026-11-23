import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

private theorem conj_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {w u : HeightOneSpectrum (𝓞 E)}
    (h : ConjPl w u) : UpperTheory.V.Af.Bc.cPl u = w := by
  obtain ⟨h1, h2⟩ := h
  by_cases e : u = w
  · subst e
    exact (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 (h2.resolve_left fun h => h rfl)
  · rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 h1.symm with h | h
    · exact absurd h.symm e
    · refine (eq_conjSrc ?_).symm
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h ⊢
      intro x y hxy
      refine (h y x ?_).symm
      rw [hxy]
      exact (IsCMField.complexConj_apply_apply E _).symm

theorem UpperTheory.V.Z.Tf.GOne.csdSat :
    CsdSat := by
  intro E _ _ _ n _ π h
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) h
  filter_upwards [GlobalTheory.T.cuspidal_satake_almost_all π] with w hw
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, hB, fun u hu => (UpperTheory.satake_parameters_complex_conjugate E u).1 n π hc B (conj_eq hu ▸ hB)⟩
