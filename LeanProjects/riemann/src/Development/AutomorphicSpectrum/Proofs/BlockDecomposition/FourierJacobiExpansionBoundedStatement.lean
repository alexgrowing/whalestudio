import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiExpansionBounded
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_expansion_bounded : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (g : G D n) (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∀ B : ℝ, (∀ y x, ‖zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))‖ ≤ B) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g))) → FJ M m ψ b₀ F g φ = ∫ v in m.𝓕 ×ˢ m.𝓕, zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) * conj (th ψ b₀ φ 0 v.2 v.1) ∂(m.μ.prod m.μ) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fj_fold_mean | exact GlobalTheory.CompanionTheory.FJE.fj_fold_mean | (intros; apply GlobalTheory.CompanionTheory.FJE.fj_fold_mean <;> assumption)
