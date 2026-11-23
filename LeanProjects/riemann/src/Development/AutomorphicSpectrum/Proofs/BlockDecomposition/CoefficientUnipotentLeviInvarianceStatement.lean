import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvariance
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_unipotent_levi_invariance : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₁ : G D p) (b : Mx D p p),
  mat g₁ = blk4 1 b 0 1 → ∀ (z₀ : hermA D ρ) (x₀ : Mx D ρ p) (x : G D n),
    Wz M m ψ b₀ f (M.nzx z₀ x₀ * M.emb g₁ * x) = chz ψ b₀ z₀ * Wz M m ψ b₀ f x := by
  first | exact @GlobalTheory.CompanionTheory.WzHeis.wz_heis | exact GlobalTheory.CompanionTheory.WzHeis.wz_heis | (intros; apply GlobalTheory.CompanionTheory.WzHeis.wz_heis <;> assumption)
