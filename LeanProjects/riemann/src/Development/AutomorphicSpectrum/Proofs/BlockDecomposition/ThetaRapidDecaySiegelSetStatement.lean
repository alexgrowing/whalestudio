import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSet
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
theorem _root_.GlobalTheory.T.theta_rapid_decay_siegel_set : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ {c : ℝ}, 0 < c → ∀ (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) ((invPt V a ξ).map (finPart D))) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilCount.count_main | exact GlobalTheory.CompanionTheory.WeilCount.count_main | (intros; apply GlobalTheory.CompanionTheory.WeilCount.count_main <;> assumption)
