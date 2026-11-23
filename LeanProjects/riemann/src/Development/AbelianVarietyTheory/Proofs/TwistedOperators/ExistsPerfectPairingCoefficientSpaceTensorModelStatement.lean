import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perfectPairing_coefficientSpace_tensorModel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  first | exact @GlobalTheory.CoefPairTens.pairEquiv_realAll | exact GlobalTheory.CoefPairTens.pairEquiv_realAll | (intros; apply GlobalTheory.CoefPairTens.pairEquiv_realAll <;> assumption)
