import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

theorem pass_isWeilSch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A T : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ)) (ν : Measure (WO A T)) (𝓨 : Set (WO A T)) (μ : D.host.E) (κ : GA D (dblSp A) ≃* GlobalTheory.StdUnn.G D A.rank) (omS : GlobalTheory.StdUnn.G D A.rank →* Module.End ℂ (schwartzA θ T.rank A.rank)), Pass ψ θ A T χ om ν 𝓨 μ κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → GlobalTheory.StdUnn.IsWeilSch (GlobalTheory.StdUnn.shift ψ lam) χ⁻¹ θ T ν omS := by
  intro D ψ θ A T χ om ν 𝓨 μ κ omS hP lam hlam
  exact
    { levi := GlobalTheory.StdUnn.transport_levi D ψ A T χ om hP.weil ν 𝓨 hP.cov θ hP.inf μ hP.skew κ hP.chart omS hP.trans lam hlam
      unip := GlobalTheory.StdUnn.Unip.transport_unip D ψ A T χ om hP.weil ν 𝓨 hP.cov θ hP.inf μ hP.skew κ hP.chart omS hP.trans lam hlam
      weyl := GlobalTheory.StdUnn.WeylStd.main D ψ A T χ om hP.weil ν 𝓨 hP.cov θ hP.inf μ hP.skew κ hP.chart omS hP.trans lam hlam }

end GlobalTheory.RegSch
