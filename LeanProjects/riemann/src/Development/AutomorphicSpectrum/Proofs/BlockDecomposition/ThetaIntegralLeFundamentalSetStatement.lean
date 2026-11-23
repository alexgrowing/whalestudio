import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_le_fundamental_set : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ {n : ℕ} (φ : Mx D V.rank n → ℂ), Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) → absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | exact GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | (intros; apply GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits <;> assumption)
