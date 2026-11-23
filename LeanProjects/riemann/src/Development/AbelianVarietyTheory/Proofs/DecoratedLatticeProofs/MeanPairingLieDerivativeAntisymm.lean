import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecr
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Ibp

variable {D : D7} {V : HSp D}

theorem isFiniteMeasure_autMeasure (m : Measure (GA D V)) [hm : m.IsHaarMeasure] :
    IsFiniteMeasure (autMeasure V m) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨by
    rw [autMeasure, quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd⟩

theorem isMulRightInvariant (m : Measure (GA D V)) [hm : m.IsHaarMeasure] : m.IsMulRightInvariant := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) m hfd (hfd.measure_ne_zero (NeZero.ne m))
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd).ne⟩

variable {θ : InfFam D} {τ : D.what₂.Tau}

end GlobalTheory.RegSch.Ibp
