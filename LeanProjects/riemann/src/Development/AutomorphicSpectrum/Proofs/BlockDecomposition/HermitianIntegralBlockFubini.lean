import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.BoxIntegrals.MeanBlocks
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_integral_block_fubini : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, IsCovolOneH lam 𝓖 → ∀ {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p → ∀ Φ : hermA D n → ℂ, Continuous Φ → IsPer Φ → ∫ b in 𝓖, Φ b ∂lam = ∫ y in 𝓖p, ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) ∂m.lz ∂m.μ ∂lp := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.mean_blocks | exact GlobalTheory.CompanionTheory.PcFc.mean_blocks | (intros; apply GlobalTheory.CompanionTheory.PcFc.mean_blocks <;> assumption)
