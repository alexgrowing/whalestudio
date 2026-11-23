import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCoefficientCongruencePullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_coefficient_congruence_pullback : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (φ : Mx D V.rank r → ℂ) (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → (∃ 𝓖, IsCovolOneH lam 𝓖) → W ψ V μ lam (pull a φ) β = W ψ V μ lam φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.W_congr | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.W_congr | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.W_congr <;> assumption)
