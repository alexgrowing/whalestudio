import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylUnipotentIwasawaHeight
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_unipotent_iwasawa_height : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ c : hermA D n, ∃ (d : GL (Fin n) (AE D)) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n ∧ mat k = blk4 k₁ k₂ k₃ k₄ ∧ d.1 * k₃ = -1 ∧ d.1 * k₄ = -c.1 ∧ (H (w * nb c))⁻¹ = absA D (Matrix.GeneralLinearGroup.det d) := by
  first | exact @GlobalTheory.CompanionTheory.HeightNu.lower_row | exact GlobalTheory.CompanionTheory.HeightNu.lower_row | (intros; apply GlobalTheory.CompanionTheory.HeightNu.lower_row <;> assumption)
