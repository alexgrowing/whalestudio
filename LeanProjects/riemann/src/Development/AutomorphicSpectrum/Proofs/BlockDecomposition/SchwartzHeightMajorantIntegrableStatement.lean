import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzHeightMajorantIntegrable
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_height_majorant_integrable : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (θ : InfFam D), IsInfFam θ →
  ∀ H : G D n → ℝ≥0, IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ Φ ∈ schwartzA θ ρ p, ∀ τ : ℝ, 0 ≤ τ → ∃ W : Mx D ρ p → ℝ, Integrable W m.μ ∧
    ∀ (x : G D n) (y : Mx D ρ p), (H (x * M.sh y) : ℝ) ^ τ * ‖Φ y‖ ≤ W y * (H x : ℝ) ^ τ := by
  first | exact @GlobalTheory.CompanionTheory.ShearGrowth.height_shear_majorant | exact GlobalTheory.CompanionTheory.ShearGrowth.height_shear_majorant | (intros; apply GlobalTheory.CompanionTheory.ShearGrowth.height_shear_majorant <;> assumption)
