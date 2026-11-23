import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderivStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockAnalytic

theorem totalDegree_pderiv_le_self {σ : Type} (i : σ) (Q : MvPolynomial σ ℂ) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  refine Finset.sup_le fun m hm => ?_
  have hc : coeff (m + Finsupp.single i 1) Q ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hm
    intro h
    rw [h, zero_mul] at hm
    exact hm rfl
  have h1 := le_totalDegree (mem_support_iff.2 hc)
  have h2 : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [h2] at h1
  show (m.sum fun _ e => e) ≤ Q.totalDegree
  omega

def OneStep {σ : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (A : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d →
    (A P).totalDegree ≤ d + 1 ∧ ‖ι (A P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2

section
variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem oneStep_mul (h : IsFockIP ι) (i : σ) : OneStep ι (LinearMap.mulLeft ℂ (X i)) := by
  intro d P hP
  refine ⟨?_, (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).1⟩
  rw [LinearMap.mulLeft_apply]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]; omega

theorem oneStep_pderiv (h : IsFockIP ι) (i : σ) : OneStep ι (pderiv i).toLinearMap := by
  intro d P hP
  refine ⟨((totalDegree_pderiv_le_self i P).trans hP).trans (Nat.le_succ _), ?_⟩
  have := (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).2
  have h2 := sq_nonneg ‖ι P‖
  change ‖ι (pderiv i P)‖ ^ 2 ≤ _
  nlinarith

omit [DecidableEq σ] in
theorem OneStep.neg {A : Module.End ℂ (MvPolynomial σ ℂ)} (h : OneStep ι A) : OneStep ι (-A) := by
  intro d P hP
  simpa using h d P hP

omit [DecidableEq σ] in
theorem OneStep.comp {A B : Module.End ℂ (MvPolynomial σ ℂ)} (hA : OneStep ι A) (hB : OneStep ι B)
    (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ((A * B) P).totalDegree ≤ d + 2 ∧ ‖ι ((A * B) P)‖ ≤ ((d : ℝ) + 3 / 2) * ‖ι P‖ := by
  obtain ⟨h1, h2⟩ := hB d P hP
  obtain ⟨h3, h4⟩ := hA (d + 1) _ h1
  refine ⟨h3, ?_⟩
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  push_cast at h4
  have h5 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (d : ℝ) + 1 + 1 by positivity)
  have h6 := sq_nonneg ‖ι P‖
  change ‖ι (A (B P))‖ ^ 2 ≤ _
  nlinarith
end

section
variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Pol p q r s →ₗ[ℂ] H}

theorem omE_bound (h : IsFockIP ι) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s)
    (hP : P.totalDegree ≤ d) :
    (omE l l' P).totalDegree ≤ d + 2 ∧ ‖ι (omE l l' P)‖ ≤ ((d : ℝ) + 2) * ‖ι P‖ := by
  have hA : OneStep ι (raiB l) := by
    unfold raiB; split_ifs
    exacts [oneStep_mul h l, (oneStep_pderiv h l).neg]
  have hB : OneStep ι (lowB l') := by
    unfold lowB; split_ifs
    exacts [oneStep_pderiv h l', oneStep_mul h l']
  obtain ⟨h1, h2⟩ := hA.comp hB d P hP
  have hn := norm_nonneg (ι P)
  unfold omE
  split_ifs
  · rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    refine ⟨(totalDegree_add _ _).trans (max_le h1 ((totalDegree_smul_le _ _).trans (by omega))), ?_⟩
    rw [map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
  · rw [add_zero]
    exact ⟨h1, by linarith⟩

theorem omAct_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ)
    (P : Pol p q r s) (hP : P.totalDegree ≤ d) :
    (omAct p q r s Y P).totalDegree ≤ d + 2 ∧
      ‖ι (omAct p q r s Y P)‖ ≤ (∑ l, ∑ l', ‖Y l l'‖) * (((d : ℝ) + 2) * ‖ι P‖) := by
  have e : omAct p q r s Y P = ∑ l, ∑ l', Y l l' • omE l l' P := by
    simp [omAct, LinearMap.sum_apply]
  rw [e]
  constructor
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l' _ => ?_)
    exact (totalDegree_smul_le _ _).trans (omE_bound h l l' d P hP).1
  · rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l' _ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (omE_bound h l l' d P hP).2 (norm_nonneg _)

theorem omAct_pow_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d m : ℕ)
    (hm : d ≤ 2 * m) (P : Pol p q r s) (hP : P.totalDegree ≤ d) (k : ℕ) :
    ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧
      ‖ι ((omAct p q r s Y ^ k) P)‖ ≤
        (2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖ := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := omAct_bound h Y _ _ ih.1
    refine ⟨by omega, h2.trans ?_⟩
    have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
    have hm' : (d : ℝ) ≤ 2 * m := by exact_mod_cast hm
    rw [Nat.ascFactorial_succ]
    push_cast
    calc _ ≤ (∑ l, ∑ l', ‖Y l l'‖) * ((2 * ((m : ℝ) + 1 + k)) *
            ((2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS
          exact mul_le_mul (by linarith) ih.2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
end

theorem omAct_pow_norm_le : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d k : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧ ‖ι ((omAct p q r s Y ^ k) P)‖ ≤ (4 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2 + 1) * ‖ι P‖ := by
  intro p q r s H _ _ ι h Y d k P hP
  obtain ⟨h1, h2⟩ := omAct_pow_bound h Y d ((d + 1) / 2) (by omega) P hP k
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  set m := (d + 1) / 2 with hm
  have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
  generalize (∑ l, ∑ l', ‖Y l l'‖) = S at hS
  have hm1 : (m : ℝ) ≤ (d : ℝ) / 2 + 1 := by
    have : 2 * m ≤ d + 2 := by omega
    have : (2 * m : ℝ) ≤ d + 2 := by exact_mod_cast this
    linarith
  have h3 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ ((d : ℝ) / 2 + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hm1
  have h4 : (((m + k).choose k : ℕ) : ℝ) ≤ 2 ^ (m + k) := by
    exact_mod_cast Nat.choose_le_two_pow (m + k) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  calc (2 * S) ^ k * ((k.factorial : ℝ) * ((m + k).choose k : ℝ))
      ≤ (2 * S) ^ k * ((k.factorial : ℝ) * 2 ^ (m + k)) := by gcongr
    _ = (4 * S) ^ k * (k.factorial : ℝ) * 2 ^ m := by
        rw [show (4 : ℝ) * S = 2 * (2 * S) by ring, mul_pow 2 (2 * S), pow_add]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.FockAnalytic
