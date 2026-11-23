import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalDecompositionStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.LatChange

theorem collapse_tagDR (D : D7) (N : ℕ) (Q : MvPolynomial (Rt D.what₂.Tau N) ℝ) :
    collapse D N (tagDR D.what₂.Tau N Q) = Q := by
  unfold collapse tagDR
  rw [aeval_rename]
  exact aeval_X_left_apply Q

theorem tagDR_whom (Tau : Type) [Fintype Tau] (N m : ℕ) (Q : MvPolynomial (Rt Tau N) ℝ) (h : Q.IsHomogeneous m) :
    (tagDR Tau N Q).IsWeightedHomogeneous (LatticeTransfer.wt Tau N) m := by
  unfold tagDR
  have h' : Q.IsWeightedHomogeneous (1 : Rt Tau N → ℕ) m := h
  rw [Q.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ (fun d hd => ?_)
  rw [rename_monomial]
  refine isWeightedHomogeneous_monomial _ _ _ ?_
  rw [← h' (mem_support_iff.1 hd)]
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intro b m₁ m₂; rw [add_smul])]
  rfl

theorem le_dim (ι : Type) [Fintype ι] (τ : ι) (N k : ℕ) (hk : k ≤ N) : k ≤ dimFl ι N + 1 := by
  unfold dimFl
  have h1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨τ⟩
  have h2 : N ≤ N * (N - 1) / 2 + 1 := by
    rcases N with _ | _ | n
    · simp
    · simp
    · have : n + 1 ≤ (n + 1 + 1) * (n + 1 + 1 - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        simp only [Nat.add_sub_cancel]
        nlinarith
      omega
  have h3 : N * (N - 1) / 2 ≤ Fintype.card ι * (N * (N - 1) / 2) := Nat.le_mul_of_pos_left _ h1
  omega

theorem chLie_zero {D : D7} (N j : ℕ) (hj : j ≤ N) (σ : EmbC D) :
    chLie (D := D) (N := N) j 0 σ = C (σ.elim (fun _ => (j : ℝ)) (fun _ => (N : ℝ) - j)) := by
  have hl : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j := by
    rw [Fin.card_filter_val_lt]; omega
  have hr : (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun i : Fin N => (i : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rcases σ with τ | τ
  · simp only [chLie, pow_zero, Finset.sum_const, hl, Sum.elim_inl]
    simp
  · simp only [chLie, pow_zero, Finset.sum_const, hr, Sum.elim_inr]
    rw [← Nat.cast_sub hj]
    simp

end GlobalTheory.LatChange
