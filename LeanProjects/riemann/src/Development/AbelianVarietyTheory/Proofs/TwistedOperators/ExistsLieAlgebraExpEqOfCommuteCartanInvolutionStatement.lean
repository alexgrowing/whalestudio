import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieAlgebraExpEqOfCommuteCartanInvolution
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieAlgebra_exp_eq_of_commute_cartanInvolution : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C → ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  first | exact @GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan | exact GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan | (intros; apply GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan <;> assumption)
