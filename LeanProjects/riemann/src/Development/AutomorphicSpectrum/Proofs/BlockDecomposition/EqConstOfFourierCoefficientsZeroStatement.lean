import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZero
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_const_of_fourier_coefficients_zero : ∀ {D : D7} {p : ℕ} {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p → ∀ {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ φ : hermA D p → ℂ, Continuous φ → IsPer φ → (∀ a : HermE D p, a.1 ≠ 0 → ∫ y in 𝓖p, φ y * chn ψ a y ∂lp = 0) → ∀ y, φ y = φ 0 := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.const_of_coeff | exact GlobalTheory.CompanionTheory.PcFc.const_of_coeff | (intros; apply GlobalTheory.CompanionTheory.PcFc.const_of_coeff <;> assumption)
