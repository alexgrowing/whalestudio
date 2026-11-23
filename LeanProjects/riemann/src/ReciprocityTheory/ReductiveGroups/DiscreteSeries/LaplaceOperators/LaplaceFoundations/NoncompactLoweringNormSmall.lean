import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.DoubleSumDiagSplit

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

def highestWeightBoundConst {n : ℕ} (ε : Fin n → Bool) (d Λ₀ : Fin n → ℝ) : ℝ :=
  |nsq (rho n) - nsq (rhoN ε - rhoC ε)| + 2 * ∑ a, |d a| + 2 * ∑ a, |Λ₀ a| + 1

theorem one_le_highestWeightBoundConst {n : ℕ} (ε : Fin n → Bool) (d Λ₀ : Fin n → ℝ) : 1 ≤ highestWeightBoundConst ε d Λ₀ := by
  unfold highestWeightBoundConst
  have h1 : 0 ≤ ∑ a, |d a| := sum_nonneg fun a _ => abs_nonneg _
  have h2 : 0 ≤ ∑ a, |Λ₀ a| := sum_nonneg fun a _ => abs_nonneg _
  have h3 := abs_nonneg (nsq (rho n) - nsq (rhoN ε - rhoC ε))
  linarith

theorem le_mul_of_sq_le_mul_sq {x C s : ℝ} (_hx : 0 ≤ x) (hC : 1 ≤ C) (hs : 1 ≤ s) (h : x ^ 2 ≤ C * s ^ 2) :
    x ≤ C * s := by
  have h1 : C * s ^ 2 ≤ (C * s) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ C - 1) (by linarith : (0:ℝ) ≤ C))
      (sq_nonneg s)]
  have h2 : 0 ≤ C * s := by positivity
  nlinarith

section Datum

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {w : M}

theorem noncompact_lowering_norm_small (hw : IsHWDatum ε E lam w) {a b : Fin n} (hab : a < b) (hne : ε a ≠ ε b) :
    ‖E b a w‖ ^ 2 ≤ |nsq (rho n) - nsq (rhoN ε - rhoC ε)| := by
  have hb := b2Id
  unfold RaisingLoweringNormIdentities at hb
  have h3 := (hb n ε M E lam w hw).2.2
  have h1 : ‖E b a w‖ ^ 2 ≤ ∑ b' ∈ univ.filter (fun b' => a < b' ∧ ε a ≠ ε b'), ‖E b' a w‖ ^ 2 :=
    single_le_sum (f := fun b' => ‖E b' a w‖ ^ 2) (fun _ _ => sq_nonneg _) (by simp [hab, hne])
  have h2 : (∑ b' ∈ univ.filter (fun b' => a < b' ∧ ε a ≠ ε b'), ‖E b' a w‖ ^ 2) ≤
      ∑ a', ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2 :=
    single_le_sum (f := fun a' => ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2)
      (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ a)
  have h4 : 0 ≤ ∑ a', ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h5 := le_abs_self (nsq (rho n) - nsq (rhoN ε - rhoC ε))
  linarith

theorem highest_weight_datum_bounds {d Λ₀ : Fin n → ℝ} {t : ℝ} (ht : 1 ≤ t) (hw : IsHWDatum ε E lam w)
    (hΛ : lowK ε lam = t • d + Λ₀) :
    (∀ a b, InNP ε d a b → ‖E a b w‖ ≤ highestWeightBoundConst ε d Λ₀) ∧
      (∀ a b, InLL ε d a b →
        ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ highestWeightBoundConst ε d Λ₀) ∧
      ∀ X : Matrix (Fin n) (Fin n) ℂ,
        ‖actM E X w - ((t : ℂ) * trace (dMat d * X)) • w‖ ≤
          highestWeightBoundConst ε d Λ₀ * Real.sqrt t * l1 X := by
  have hb := b2Id
  unfold RaisingLoweringNormIdentities at hb
  obtain ⟨hI1, hI2, -⟩ := hb n ε M E lam w hw
  have hw1 : ‖w‖ = 1 := hw.2.2.1
  have hdiag : ∀ a, E a a w = ((lowK ε lam a : ℝ) : ℂ) • w := hw.2.2.2.1.1
  have hup : ∀ a b, a < b → ε a = ε b → E a b w = 0 := hw.2.2.2.1.2
  set C := highestWeightBoundConst ε d Λ₀ with hCdef
  set K0 := nsq (rho n) - nsq (rhoN ε - rhoC ε) with hK0
  set S := ∑ a, |d a| with hS
  set T := ∑ a, |Λ₀ a| with hT
  have hC1 : 1 ≤ C := one_le_highestWeightBoundConst ε d Λ₀
  have hCe : C = |K0| + 2 * S + 2 * T + 1 := rfl
  have hS0 : 0 ≤ S := sum_nonneg fun a _ => abs_nonneg _
  have hT0 : 0 ≤ T := sum_nonneg fun a _ => abs_nonneg _
  have hK0a := abs_nonneg K0
  have hdS : ∀ a, |d a| ≤ S := fun a =>
    single_le_sum (f := fun a => |d a|) (fun _ _ => abs_nonneg _) (mem_univ a)
  have hΛT : ∀ a, |Λ₀ a| ≤ T := fun a =>
    single_le_sum (f := fun a => |Λ₀ a|) (fun _ _ => abs_nonneg _) (mem_univ a)
  have hL : ∀ a, lowK ε lam a = t * d a + Λ₀ a := by
    intro a; rw [hΛ]; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ht0 : 0 ≤ t := by linarith
  have hdiff : ∀ a b, lowK ε lam a - lowK ε lam b ≤ (2 * S + 2 * T) * t := by
    intro a b
    rw [hL, hL]
    have e1 : t * d a ≤ t * |d a| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0
    have e2 : -(t * d b) ≤ t * |d b| := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le (d b)) ht0; linarith
    have e3 := le_abs_self (Λ₀ a)
    have e4 := neg_abs_le (Λ₀ b)
    have e5 : t * |d a| ≤ t * S := mul_le_mul_of_nonneg_left (hdS a) ht0
    have e6 : t * |d b| ≤ t * S := mul_le_mul_of_nonneg_left (hdS b) ht0
    have e7 := hΛT a
    have e8 := hΛT b
    have e9 : T ≤ T * t := by nlinarith
    nlinarith
  have hsqb : ∀ a b, a ≠ b → ‖E a b w‖ ^ 2 ≤ C * t := by
    intro a b hab
    have hKt : |K0| ≤ |K0| * t := by nlinarith
    rcases lt_or_gt_of_ne hab with h | h <;> by_cases he : ε a = ε b
    · rw [hup a b h he]; simp; positivity
    · have h1 := hI2 a b h he
      have h2 := noncompact_lowering_norm_small hw h he
      have h3 := hdiff a b
      rw [h1]; nlinarith
    · have h1 := hI1 b a h he.symm
      have h3 := hdiff b a
      rw [h1]; nlinarith
    · have h2 := noncompact_lowering_norm_small hw h (Ne.symm he)
      nlinarith
  have hsq1 : 1 ≤ Real.sqrt t := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt ht
  have hsq2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  have hdg : ∀ a, ‖E a a w - (((t * d a : ℝ)) : ℂ) • w‖ = |Λ₀ a| := by
    intro a
    rw [hdiag a, ← sub_smul, ← Complex.ofReal_sub, norm_smul, hw1, mul_one, hL a]
    rw [show t * d a + Λ₀ a - t * d a = Λ₀ a by ring, Complex.norm_real, Real.norm_eq_abs]
  have hentry : ∀ a b,
      ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ C * Real.sqrt t := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, hdg]
      have := hΛT a
      nlinarith
    · rw [if_neg hab, zero_smul, sub_zero]
      exact le_mul_of_sq_le_mul_sq (norm_nonneg _) hC1 hsq1 (by rw [hsq2]; exact hsqb a b hab)
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    rcases hab with ⟨h, he, -⟩ | ⟨h, he⟩
    · rw [hup a b h he, norm_zero]; linarith
    · have h2 := noncompact_lowering_norm_small hw h (Ne.symm he)
      have := le_mul_of_sq_le_mul_sq (norm_nonneg (E a b w)) hC1 le_rfl (by nlinarith)
      linarith
  · intro a b hab
    obtain ⟨he, hd⟩ := hab
    by_cases h0 : a = b
    · subst h0
      rw [if_pos rfl, hdg]
      have := hΛT a
      linarith
    · rw [if_neg h0, zero_smul, sub_zero]
      rcases lt_or_gt_of_ne h0 with h | h
      · rw [hup a b h he, norm_zero]; linarith
      · have h1 := hI1 b a h he.symm
        rw [hL, hL, hd] at h1
        have e7 := hΛT a
        have e8 := hΛT b
        have e3 := neg_abs_le (Λ₀ a)
        have e4 := le_abs_self (Λ₀ b)
        have := le_mul_of_sq_le_mul_sq (norm_nonneg (E a b w)) hC1 le_rfl (by rw [h1]; nlinarith)
        linarith
  · intro X
    have key : actM E X w - ((t : ℂ) * trace (dMat d * X)) • w =
        ∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      congr 1
      · simp [actM, LinearMap.sum_apply]
      · simp only [Matrix.trace, dMat, Matrix.diag, Matrix.diagonal_mul, ite_smul, zero_smul,
          smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_smul,
          Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        push_cast
        ring
    rw [key]
    calc ‖∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w)‖
        ≤ ∑ a, ∑ b, ‖X a b‖ * (C * Real.sqrt t) :=
          (norm_sum_le _ _).trans (sum_le_sum fun a _ => (norm_sum_le _ _).trans
            (sum_le_sum fun b _ => by
              rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hentry a b) (norm_nonneg _)))
      _ = C * Real.sqrt t * l1 X := by
          unfold l1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring

end Datum

theorem b2 : HighestWeightVectorUniformBounds := by
  intro n ε d Λ₀
  refine ⟨highestWeightBoundConst ε d Λ₀, le_trans zero_le_one (one_le_highestWeightBoundConst ε d Λ₀), ?_⟩
  intro t ht M _ _ E lam w hw hΛ
  exact highest_weight_datum_bounds ht hw hΛ

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
