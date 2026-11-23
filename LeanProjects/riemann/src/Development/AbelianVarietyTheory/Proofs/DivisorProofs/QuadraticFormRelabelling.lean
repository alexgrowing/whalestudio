import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

namespace GlobalTheory.RelabDR
variable {D : D7} (O : Setup D)

theorem wholeL_bijective_sqs : Function.Bijective (wholeL O) := by
  have hnd := GlobalTheory.Proof.LetterConjugation.nodup_letters O.S.Dw
  have h1 : Function.Bijective (letters O.S.Dw).get :=
    ⟨List.nodup_iff_injective_get.1 hnd, fun x => List.get_of_mem (GlobalTheory.Proof.LetterConjugation.mem_letters O.S.Dw x)⟩
  exact h1.comp (finCongr (GlobalTheory.ShFam.Pad.length_letters O.S).symm).bijective

theorem rootL_bijective_sqs : Function.Bijective (rootL O) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨GlobalTheory.ShFam.Pad.LieGen.rootLetter_injective O.S,
    (Fintype.card_of_bijective (GlobalTheory.ShFam.Pad.LieGen.rootIdx_bijective O.S)).trans
      (Fintype.card_of_bijective (wholeL_bijective_sqs O))⟩

theorem sg_sq_real (i : GlobalTheory.EigWhole.Var O) : ((sg O i : ℝ)) ^ 2 = 1 := by
  rcases i with x | k | k
  · simp only [sg, rootSg]; split_ifs <;> norm_num
  · simp [sg]
  · simp [sg]

theorem aeval_halfWholeSq_sub_rootSq : ∀ (D : D7) (O : Setup D), aeval (fun i => (C (GlobalTheory.RelabDR.sg O i : ℝ) * X (GlobalTheory.RelabDR.ix O i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ)) (C (1 / 2 : ℝ) * ∑ l, X (Sum.inr l) ^ 2 - ∑ x, X (Sum.inl x) ^ 2 : MvPolynomial (GlobalTheory.EigWhole.Var O) ℝ) = ∑ z, X (Sum.inr z) ^ 2 - ∑ z, X (Sum.inl z) ^ 2 := by
  intro D O
  have hsq : ∀ i, (C (GlobalTheory.RelabDR.sg O i : ℝ) * X (GlobalTheory.RelabDR.ix O i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) ^ 2 = X (GlobalTheory.RelabDR.ix O i) ^ 2 := by
    intro i
    rw [mul_pow, ← C_pow, GlobalTheory.RelabDR.sg_sq_real, C_1, one_mul]
  simp only [map_sub, map_mul, map_sum, map_pow, aeval_X, aeval_C, hsq]
  have hW : ∑ k, (X (Sum.inr (GlobalTheory.RelabDR.wholeL O k)) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) ^ 2 = ∑ z, X (Sum.inr z) ^ 2 :=
    Fintype.sum_bijective _ (GlobalTheory.RelabDR.wholeL_bijective_sqs O) _ _ (fun _ => rfl)
  have hR : ∑ x, (X (Sum.inl (GlobalTheory.RelabDR.rootL O x)) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) ^ 2 = ∑ z, X (Sum.inl z) ^ 2 :=
    Fintype.sum_bijective _ (GlobalTheory.RelabDR.rootL_bijective_sqs O) _ _ (fun _ => rfl)
  have hRev : ∑ k : Fin (D.R.f * O.N), (X (Sum.inr (GlobalTheory.RelabDR.wholeL O (Fin.rev k))) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) ^ 2 = ∑ k, X (Sum.inr (GlobalTheory.RelabDR.wholeL O k)) ^ 2 :=
    Equiv.sum_comp Fin.revPerm (fun k => (X (Sum.inr (GlobalTheory.RelabDR.wholeL O k)) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) ^ 2)
  rw [Fintype.sum_sum_type]
  simp only [GlobalTheory.RelabDR.ix]
  have h2 : (C (1/2 : ℝ) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  rw [hRev, hW, hR, algebraMap_eq, ← two_mul, ← mul_assoc, h2, one_mul]

end GlobalTheory.RelabDR
