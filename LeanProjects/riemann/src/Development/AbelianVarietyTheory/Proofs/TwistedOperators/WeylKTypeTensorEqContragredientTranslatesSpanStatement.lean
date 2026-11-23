import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_kTypeTensor_eq_contragredient_translatesSpan : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, FiniteDimensional ℂ (H τ)] (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (lamH : ι → Fin n → ℝ) (lam : ι → ℕ → ℤ), (∀ τ, StrictAnti (lamH τ)) → (∀ τ, Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) (σ τ)) → (∀ τ, Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) (σ τ) (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) ⊤) → (∀ τ (i : Fin n), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) (Fin.rev i)) → ∃ Φ : Module.Dual ℂ (weylSub n lam) ≃ₗ[ℂ] ⨂[ℂ] τ, H τ, ∀ (u : UG ι n) (φ : Module.Dual ℂ (weylSub n lam)), Φ ((weylRep n lam).dual u φ) = PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) (Φ φ) := by
  first | exact @GlobalTheory.DualWeylTensor.main | exact GlobalTheory.DualWeylTensor.main | (intros; apply GlobalTheory.DualWeylTensor.main <;> assumption)
