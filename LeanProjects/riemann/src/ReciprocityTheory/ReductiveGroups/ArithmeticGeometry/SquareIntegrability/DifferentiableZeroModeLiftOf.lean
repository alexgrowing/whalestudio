import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.UQEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAC

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

theorem norm_uc_sq {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι) :
    ‖uc K v‖ ^ 2 = ∑ k, (z K k v).im ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_uc _ v _ (uc_mem _ v), uc, Hf_sum_r, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_rsmul_r, Complex.im_ofReal_mul, z]; ring

theorem re_S {ι : Type} [Fintype ι] {K : Submodule ℝ (EuclideanSpace ℂ ι)}
    (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0) (w : EuclideanSpace ℂ ι) :
    (S K w).re = ‖w‖ ^ 2 - ‖p2 K w‖ ^ 2 - 2 * ‖uc K w‖ ^ 2 := by
  rw [norm_sq_decomp hK, norm_uc_sq, S, Complex.re_sum]
  have hz : ∀ k, ‖z K k w‖ ^ 2 = (z K k w).re ^ 2 + (z K k w).im ^ 2 := fun k => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [hz, sq, Complex.mul_re]
  rw [Finset.mul_sum]
  have h3 : ∑ k, ((z K k w).re * (z K k w).re - (z K k w).im * (z K k w).im) =
      ∑ k, ((z K k w).re * (z K k w).re + (z K k w).im * (z K k w).im) -
        ∑ k, 2 * ((z K k w).im * (z K k w).im) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h3]; ring

section Nsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ)
include hI

theorem norm_Tm (γ : X.L) (v : Vsp X.dim) :
    ‖Tm X I q β γ v‖ = Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(q * Real.pi) * ‖uc (IR I) (v - γ)‖ ^ 2) *
        (‖β (wmap (IR I) (v - γ))‖ * Real.exp (-(q * Real.pi) * ‖wmap (IR I) (v - γ)‖ ^ 2 / 2)) := by
  have hK := hK_of hI
  have he : ‖(X.eps (γ : Vsp X.dim) : ℂ)‖ = 1 := by
    rcases X.eps_pm _ γ.2 with h | h <;> simp [h]
  simp only [Tm, Uh, Uq, F0, norm_mul, norm_pow, he, one_pow, one_mul, Complex.norm_exp]
  set w := v - (γ : Vsp X.dim) with hw
  have h1 : (Hf v (γ : Vsp X.dim)).re = (‖v‖ ^ 2 + ‖(γ : Vsp X.dim)‖ ^ 2 - ‖w‖ ^ 2) / 2 := by
    have := Hf_self_re w
    rw [hw, Hf_sub_l, Hf_sub_r, Hf_sub_r, Complex.sub_re, Complex.sub_re, Complex.sub_re,
      Hf_self_re, Hf_self_re, Hf_swap v (γ : Vsp X.dim), Complex.conj_re] at this
    rw [← hw] at this
    linarith
  have h2 := re_S hK w
  rw [norm_wmap hK]
  have hre1 : (q * Real.pi * Hf v (γ : Vsp X.dim) - q * Real.pi * Hf (γ : Vsp X.dim) γ / 2 : ℂ).re =
      q * Real.pi * (Hf v (γ : Vsp X.dim)).re - q * Real.pi * ‖(γ : Vsp X.dim)‖ ^ 2 / 2 := by
    simp [Complex.mul_re, Hf_self_re]
  have hre2 : ((q * Real.pi / 2 : ℂ) * S (IR I) w).re = q * Real.pi / 2 * (S (IR I) w).re := by
    simp [Complex.mul_re]
  rw [hre1, hre2, h1, h2]
  rw [← mul_assoc, ← Real.exp_add, mul_comm (‖β _‖), ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem exp_shift_le (a : ℝ) (ha : 0 ≤ a) (u w : Vsp X.dim) :
    Real.exp (-a * ‖u - w‖ ^ 2) ≤ Real.exp (a * ‖u‖ ^ 2) * Real.exp (-(a / 2) * ‖w‖ ^ 2) := by
  have h1 : ‖w‖ ≤ ‖u‖ + ‖u - w‖ := by
    calc ‖w‖ = ‖u - (u - w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - w‖ := norm_sub_le _ _
  have h2 : ‖w‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖u - w‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg u, norm_nonneg (u - w), sq_nonneg (‖u‖ - ‖u - w‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

theorem cond_tail (a : ℝ) (ha : 1 / 2 ≤ a) : (dK (IR I) : ℝ) + 1 ≤ a * P.q * b0 (E := E) P.q P.R0 := by
  obtain ⟨ρ, hρm, hρ⟩ := hI.rank
  have hdK : (dK (IR I) : ℝ) ≤ dstar (E := E) P.m := by
    rw [dK, hρ, dstar]; push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hρm) (by positivity)
  have h6 := P.C6
  have hr : 0 ≤ (X.r : ℝ) * Real.log X.r := by
    rcases Nat.eq_zero_or_pos X.r with h | h
    · simp [h]
    · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast h))
  have hDF : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) := by positivity
  have hg : 0 ≤ (X.gA : ℝ) * Real.log 2 := by positivity
  have ht0 : t0 (E := E) P.q P.R0 = P.q * b0 (E := E) P.q P.R0 := rfl
  have hb := cutoff_pos P
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hqb : 0 < (P.q : ℝ) * b0 (E := E) P.q P.R0 := mul_pos hq hb
  rw [ht0] at h6
  nlinarith

theorem summable_gauss (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (a : ℝ) (ha : 1 / 2 ≤ a) :
    Summable (fun c : Qc X I => Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2)) :=
  (Finset.summable_compl_iff {0}).1 (tailQ hI hP hA a (by linarith) (cond_tail hI a ha)).1

variable {q β}

theorem norm_Tc_le {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2) (c : Qc X I) (v : Vsp X.dim) :
    ‖Tc X I q β c v‖ ≤ B * Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(q * Real.pi) * ‖uc (IR I) v - uQ X I c‖ ^ 2) := by
  rw [Tc, norm_Tm hI, uc_sub, ← uQ_out]
  have hN : ‖β (wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim)))‖ *
      Real.exp (-(q * Real.pi) * ‖wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim))‖ ^ 2 / 2) ≤ B := by
    set t := wmap (IR I) (v - ((Quotient.out c : X.L) : Vsp X.dim))
    have h := hB t
    have hsq : (‖β t‖ * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2 / 2)) ^ 2 =
        ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [← hsq] at h
    exact (pow_le_pow_iff_left₀ (by positivity) hB0 two_ne_zero).1 h
  calc _ ≤ Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2) * Real.exp (-(q * Real.pi) * ‖uc (IR I) v - uQ X I c‖ ^ 2) * B :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by ring

theorem exists_B (hS : GSupStatement) (hP : Ext.PackingCount) (hq : 1 ≤ q)
    (hβ : β ∈ (YB hI hP q).Sec q) :
    ∃ B, 0 ≤ B ∧ ∀ t, ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2 := by
  have h := hS _ (YB hI hP q) q hq β hβ
  set C := 2 * (q : ℝ) ^ Fintype.card (Fin (gB (IR I))) *
      (1 + 4 * Real.sqrt (2 * Fintype.card (Fin (gB (IR I)))) /
        (Real.sqrt (q * Real.pi) * (YB hI hP q).la1)) ^ (2 * Fintype.card (Fin (gB (IR I)))) *
      (YB hI hP q).l2 q β
  have hC : 0 ≤ C := (by unfold GT.ptN2; positivity : 0 ≤ (YB hI hP q).ptN2 q β 0).trans (h 0)
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun t => ?_⟩
  rw [Real.sq_sqrt hC]
  exact h t

omit hI in
theorem diff_Hf (a : Vsp X.dim) : Differentiable ℂ (fun v : Vsp X.dim => Hf v a) := by
  unfold Hf
  first
    | fun_prop
    | exact Differentiable.fun_sum fun i _ =>
        (EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable.mul_const _
    | exact Differentiable.sum fun i _ =>
        (EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable.mul_const _

omit hI in
theorem differentiable_zeroModeLift_of (hβd : Differentiable ℂ β) : Differentiable ℂ (F0 I q β) := by
  unfold F0
  apply Differentiable.mul
  · apply Differentiable.cexp
    apply Differentiable.const_mul
    unfold S z
    exact Differentiable.fun_sum (fun k _ => (diff_Hf _).pow 2)
  · exact hβd.comp (wmap (IR I)).differentiable

omit hI in
theorem diff_Tm (hβd : Differentiable ℂ β) (γ : Vsp X.dim) : Differentiable ℂ (Uh X q γ (F0 I q β)) := by
  unfold Uh Uq
  apply Differentiable.const_mul
  apply Differentiable.mul
  · apply Differentiable.cexp
    exact ((diff_Hf γ).const_mul _).sub_const _
  · exact (differentiable_zeroModeLift_of hβd).comp (differentiable_id.sub_const γ)

end Nsec

section Ssec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
  {β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ} (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound)
  {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2)
include hI hP hA hB0 hB

theorem Tc_bound (R : ℝ) (c : Qc X I) (v : Vsp X.dim) (hv : ‖v‖ ≤ R) :
    ‖Tc X I P.q β c v‖ ≤ B * Real.exp (P.q * Real.pi * R ^ 2 / 2) *
      (Real.exp (P.q * Real.pi * R ^ 2) * Real.exp (-(Real.pi / 2 * P.q) * ‖uQ X I c‖ ^ 2)) := by
  have hq : (0 : ℝ) ≤ P.q * Real.pi := by positivity
  have hv2 : ‖v‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have hu2 : ‖uc (IR I) v‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((norm_uc_le hI.iso v).trans hv) 2
  refine (norm_Tc_le hI hB0 hB c v).trans ?_
  rw [mul_assoc, mul_assoc B]
  apply mul_le_mul_of_nonneg_left _ hB0
  apply mul_le_mul (Real.exp_le_exp.2 (by nlinarith)) _ (by positivity) (by positivity)
  refine (exp_shift_le hI (P.q * Real.pi) hq _ _).trans ?_
  apply mul_le_mul (Real.exp_le_exp.2 (by nlinarith)) (le_of_eq ?_) (by positivity) (by positivity)
  congr 1; ring

theorem summable_Tc (v : Vsp X.dim) : Summable (fun c : Qc X I => Tc X I P.q β c v) := by
  refine Summable.of_norm_bounded ?_ (fun c => Tc_bound hI hP hA hB0 hB ‖v‖ c v le_rfl)
  exact ((summable_gauss hI hP hA (Real.pi / 2) (by linarith [Real.pi_gt_three])).mul_left _).mul_left _

theorem diff_sP (hβd : Differentiable ℂ β) : Differentiable ℂ (sP X I P.q β) := by
  intro x
  have hb : ∀ R : ℝ, ∃ u : Qc X I → ℝ, Summable u ∧
      ∀ c v, ‖v‖ ≤ R → ‖Tc X I P.q β c v‖ ≤ u c := by
    intro R
    exact ⟨_, ((summable_gauss hI hP hA (Real.pi / 2) (by linarith [Real.pi_gt_three])).mul_left
      (Real.exp (P.q * Real.pi * R ^ 2))).mul_left (B * Real.exp (P.q * Real.pi * R ^ 2 / 2)),
      fun c v hv => Tc_bound hI hP hA hB0 hB R c v hv⟩
  exact (pa_tsum_hasFDeriv (fun c => Tc X I P.q β c)
    (fun c => diff_Tm (q := P.q) hβd _) hb x).2.differentiableAt

def colS (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (gB (IR I))) → ℂ) :
    (Fin 1 → Vsp X.dim) → ℂ :=
  fun w => sP X I q β (w 0)

theorem colS_mem (hβ : β ∈ (YB hI hP P.q).Sec P.q) : colS X I P.q β ∈ X.Sec P.q 1 := by
  refine ⟨(diff_sP hI hP hA hB0 hB hβ.1).comp (differentiable_apply 0), fun γ hγ v => ?_⟩
  have h := sP_shift hI hP P.q hβ ⟨γ 0, hγ 0⟩ (v 0)
  simp only [colS, Pi.add_apply, Fin.prod_univ_one, HC, Fin.sum_univ_one]
  exact h

end Ssec

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
