import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelabDR

theorem rootL_bijective_lam {D : D7} (O : Setup D) : Function.Bijective (rootL O) := by
  classical
  have h := LieGen.rootIdx_bijective O.S
  unfold LieGen.rootIdx at h
  exact (Function.Bijective.of_comp_iff' (Equiv.bijective ((((GlobalTheory.Proof.LetterConjugation.nodup_letters O.S.Dw).getEquivOfForallMemList _
    (GlobalTheory.Proof.LetterConjugation.mem_letters O.S.Dw)).symm).trans (finCongr (length_letters O.S)))) _).1 h

theorem aeval_rootSub_lamA : ∀ (D : D7) (O : Setup D),
    aeval (GlobalTheory.RelabDR.rootSub O) (lamA D.what₂.Tau O.N O.j) = -∑ z, X z := by
  intro D O
  rw [← (rootL_bijective_lam O).sum_comp (fun z => (X z : MvPolynomial _ ℝ)), Fintype.sum_prod_type,
    ← Finset.sum_neg_distrib, lamA, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [pHigh, pLow, pow_one, map_sub, map_sum, aeval_X, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < O.j
  · simp [hi, not_le.2 hi, rootSub, rootSg]
  · simp [hi, not_lt.1 hi, rootSub, rootSg]

end GlobalTheory.RelabDR

end
