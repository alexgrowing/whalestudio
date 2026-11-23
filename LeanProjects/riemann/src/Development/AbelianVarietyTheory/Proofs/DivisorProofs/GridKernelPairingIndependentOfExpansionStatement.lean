import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridKernelPairingIndependentOfExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridKernelPairing_independent_of_expansion : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (μ₀ : T), L.Is μ₀ → ∀ t ∈ U, ∀ Φ : G.Datum, (∀ β τ, S.IsExpansion t Φ β τ → ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) ∧ ∀ β τ τ', S.IsExpansion t Φ β τ → S.IsExpansion t Φ β τ' → ∀ c : S.Classes t Φ β, S.pairAt τ c = S.pairAt τ' c := by
  first | exact @GlobalTheory.FunObj.sumOK_vec_indep | exact GlobalTheory.FunObj.sumOK_vec_indep | (intros; apply GlobalTheory.FunObj.sumOK_vec_indep <;> assumption)
