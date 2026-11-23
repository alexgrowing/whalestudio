import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
open scoped TensorProduct Kronecker

noncomputable section

open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory.KFixIrr.LowStable

theorem deg_X_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (X a * pderiv b P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (le_totalDegree hs)
    rw [X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

theorem deg_pderiv_X {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (pderiv b (X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (totalDegree_add _ _).trans (max_le (deg_X_pderiv _ _ _) ?_)
  rw [pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (totalDegree_smul_le _ _).trans (h P)

theorem mem_nonRaising {σ : Type} {L : Module.End ℂ (MvPolynomial σ ℂ)} :
    L ∈ nonRaising σ ↔ ∀ P, (L P).totalDegree ≤ P.totalDegree := Iff.rfl

theorem rl_pos {P Q R S : ℕ} (l l' : Ln P Q R S) (hl : linePos l = true) (hl' : linePos l' = true) :
    raiB l * lowB l' ∈ nonRaising (Ln P Q R S) := by
  refine mem_nonRaising.2 fun g => ?_
  rw [Module.End.mul_apply, raiB, lowB, if_pos hl, if_pos hl', LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  exact deg_X_pderiv _ _ _

theorem rl_neg {P Q R S : ℕ} (l l' : Ln P Q R S) (hl : linePos l = false) (hl' : linePos l' = false) :
    raiB l * lowB l' ∈ nonRaising (Ln P Q R S) := by
  refine mem_nonRaising.2 fun g => ?_
  rw [Module.End.mul_apply, raiB, lowB, if_neg (by simp [hl]), if_neg (by simp [hl']), LinearMap.mulLeft_apply,
    LinearMap.neg_apply, Derivation.coeFn_coe, totalDegree_neg]
  exact deg_pderiv_X _ _ _

theorem omE_mem {P Q R S : ℕ} (l l' : Ln P Q R S) (h : linePos l = linePos l') :
    omE l l' ∈ nonRaising (Ln P Q R S) := by
  rw [omE]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · exact rl_neg l l' hl (h ▸ hl)
    · exact rl_pos l l' hl (h ▸ hl)
  · split_ifs
    · exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun g => le_rfl)
    · exact Submodule.zero_mem _

theorem linePos_same {P Q R S : ℕ} (a : Ix P Q) (c d : Ix R S) (h : sameBlock c d) :
    linePos ((a, c) : Ln P Q R S) = linePos (a, d) := by
  rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock, linePos]

theorem fockAct2_mem {P Q R S : ℕ} (Z : Mat R S) (hZ : IsKC Z) :
    fockAct2 P Q R S Z ∈ nonRaising (Ln P Q R S) := by
  classical
  rw [show fockAct2 P Q R S Z = omAct P Q R S ((1 : Mat P Q) ⊗ₖ Z) from rfl, omAct_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => ?_
  rcases l with ⟨a, c⟩
  rcases l' with ⟨a', d⟩
  rw [Matrix.kroneckerMap_apply]
  by_cases ha : a = a'
  · subst ha
    by_cases hcd : sameBlock c d
    · exact Submodule.smul_mem _ _ (omE_mem _ _ (linePos_same a c d hcd))
    · rw [hZ c d hcd, mul_zero, zero_smul]; exact Submodule.zero_mem _
  · rw [Matrix.one_apply_ne ha, zero_mul, zero_smul]; exact Submodule.zero_mem _

theorem fockAct2_lowOne : ∀ (P Q R S : ℕ) (x : ℚ) (d : ℕ) (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z →
    ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d, Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d := by
  intro P Q R S x d Z hZ f hf
  rw [mem_lowOne] at hf ⊢
  refine ⟨?_, (mem_nonRaising.1 (fockAct2_mem Z hZ) f).trans hf.2⟩
  rw [mem_chiOne] at hf ⊢
  intro X hX
  have h := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute P Q R S).2.2 X Z) f
  simp only [Module.End.mul_apply] at h
  rw [h, hf.1 X hX, map_smul]

end GlobalTheory.KFixIrr.LowStable

end
