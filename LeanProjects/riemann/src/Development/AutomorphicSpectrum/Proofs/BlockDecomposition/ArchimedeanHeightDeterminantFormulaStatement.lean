import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHeightDeterminantFormula
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
theorem _root_.GlobalTheory.T.archimedean_height_determinant_formula : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₁ k₂ k₃ k₄ : Mx D n n) (τ : D.what₂.Tau), (blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)) * ((blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)))ᴴ = 1 → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → (1 + (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ) * (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ)).det.re = ‖θ τ (infPart D (Matrix.GeneralLinearGroup.det d).1)‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.MM.RealId.det_one_add_sq | exact GlobalTheory.CompanionTheory.MM.RealId.det_one_add_sq | (intros; apply GlobalTheory.CompanionTheory.MM.RealId.det_one_add_sq <;> assumption)
