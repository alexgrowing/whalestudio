import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFundamentalDomainVolumeLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureAll

theorem oneMeasure : Hypotheses2 → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  intro hP D Tu C t0 hC i P
  refine ⟨GlobalTheory.T.level_index_bound_of_classicalTheorems hP D Tu C t0 hC i P, fun τ => GlobalTheory.T.one_le_dimAt' D i τ, fun μ 𝓕 hF =>
    ⟨GlobalTheory.T.fundamental_domain_measure_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF, GlobalTheory.T.fundamental_domain_measure_ne_top hP D Tu C t0 hC i P μ 𝓕 hF,
      GlobalTheory.T.exact_ratio_of_fundamental_domain hP D Tu C t0 hC i P μ 𝓕 hF, fun L hL =>
        ⟨fun τ => GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL τ, GlobalTheory.T.log_fundamental_domain_volume_le hP D Tu C t0 hC i P μ 𝓕 hF L hL,
          GlobalTheory.T.log_measure_ratio_le hP D Tu C t0 hC i P μ 𝓕 hF L hL⟩⟩⟩

end GlobalTheory.OneMeasureAll
