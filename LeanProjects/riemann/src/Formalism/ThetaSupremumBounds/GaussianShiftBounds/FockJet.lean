import Mathlib
import Formalism.ThetaSupremumBounds.StatementA

open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat

noncomputable section

namespace Formalism.DimensionVariation

theorem fjMoment (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) ∧
    ∫ z : ℂ, ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2) =
      π * b ^ (-((n : ℝ) + 2) / 2) * Real.Gamma (((n : ℝ) + 2) / 2) := by
  have hval : ∫ z : ℂ, ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2) =
      π * b ^ (-((n : ℝ) + 2) / 2) * Real.Gamma (((n : ℝ) + 2) / 2) := by
    have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ)) (b := b)
      (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hb
    simp only [Real.rpow_two, Real.rpow_natCast] at h
    rw [h]
    ring
  refine ⟨Integrable.of_integral_ne_zero ?_, hval⟩
  rw [hval]
  have h1 : 0 < b ^ (-((n : ℝ) + 2) / 2) := Real.rpow_pos_of_pos hb _
  have h2 : 0 < Real.Gamma (((n : ℝ) + 2) / 2) := Real.Gamma_pos_of_pos (by positivity)
  exact (mul_pos (mul_pos Real.pi_pos h1) h2).ne'

def fjChi (N : ℕ) (z : ℂ) : ℂ := if ‖z‖ ≤ N then 1 else 0

theorem fjChi_measurable (N : ℕ) : Measurable (fjChi N) := by
  show Measurable fun z : ℂ => if ‖z‖ ≤ (N : ℝ) then (1 : ℂ) else 0
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_const
    measurable_const

theorem fjChi_norm_le (N : ℕ) (z : ℂ) : ‖fjChi N z‖ ≤ 1 := by
  unfold fjChi
  split_ifs <;> simp

def fjW (a b : ℕ) (z : ℂ) : ℂ := z ^ a * conj z ^ b * (Real.exp (-‖z‖ ^ 2) : ℂ)

theorem fjW_continuous (a b : ℕ) : Continuous (fjW a b) := by
  show Continuous fun z : ℂ => z ^ a * conj z ^ b * (Real.exp (-‖z‖ ^ 2) : ℂ)
  exact ((continuous_id.pow a).mul (Complex.continuous_conj.pow b)).mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_norm.pow 2).neg))

theorem fjW_norm (a b : ℕ) (z : ℂ) : ‖fjW a b z‖ = ‖z‖ ^ (a + b) * Real.exp (-1 * ‖z‖ ^ 2) := by
  rw [fjW, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_add, neg_one_mul]

theorem fjW_integrable (a b : ℕ) : Integrable (fjW a b) :=
  (fjMoment 1 one_pos (a + b)).1.mono'
    (fjW_continuous a b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (fjW_norm a b z).le)

theorem fjW_diag (n : ℕ) : ∫ z : ℂ, fjW n n z = (π : ℂ) * (n ! : ℂ) := by
  have h : ∀ z : ℂ, fjW n n z =
      ((‖z‖ ^ (2 * n) * Real.exp (-1 * ‖z‖ ^ 2) : ℝ) : ℂ) := by
    intro z
    rw [neg_one_mul, Complex.ofReal_mul, Complex.ofReal_pow, pow_mul, fjW, ← mul_pow,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [h]
  rw [integral_complex_ofReal, (fjMoment 1 one_pos (2 * n)).2]
  have hG : ((((2 * n : ℕ) : ℝ) + 2) / 2) = (n : ℝ) + 1 := by push_cast; ring
  rw [hG, Real.one_rpow, mul_one, Real.Gamma_nat_eq_factorial, Complex.ofReal_mul,
    Complex.ofReal_natCast]

private theorem integral_comp_mul_of_norm_eq_one (g : ℂ → ℂ) (w : ℂ) (hw : ‖w‖ = 1) :
    ∫ z : ℂ, g (w * z) = ∫ z : ℂ, g z := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hw
    exact zero_ne_one hw
  let L : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toFun := fun z => w * z
      invFun := fun z => w⁻¹ * z
      map_add' := fun x y => mul_add w x y
      map_smul' := fun r z => mul_smul_comm r w z
      left_inv := fun z => inv_mul_cancel_left₀ hw0 z
      right_inv := fun z => mul_inv_cancel_left₀ hw0 z
      norm_map' := fun z => by
        show ‖w * z‖ = ‖z‖
        rw [norm_mul, hw, one_mul] }
  exact L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding g

theorem fjOrth (N a b : ℕ) (hab : a ≠ b) : ∫ z : ℂ, fjChi N z * fjW a b z = 0 := by
  have hab' : ((a : ℝ) - b) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  obtain ⟨θ, hθπ⟩ : ∃ θ : ℝ, ((a : ℂ) - b) * (θ : ℂ) = π := by
    refine ⟨π / ((a : ℝ) - b), ?_⟩
    have h : ((a : ℝ) - b) * (π / ((a : ℝ) - b)) = π := by field_simp
    exact_mod_cast h
  obtain ⟨w, hw1, hwab⟩ : ∃ w : ℂ, ‖w‖ = 1 ∧ w ^ a * conj w ^ b = -1 := by
    refine ⟨Complex.exp (θ * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_⟩
    rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_pi_mul_I]
    congr 1
    linear_combination Complex.I * hθπ
  have hpt : ∀ z : ℂ, fjChi N (w * z) * fjW a b (w * z) =
      -(fjChi N z * fjW a b z) := by
    intro z
    have hn : ‖w * z‖ = ‖z‖ := by rw [norm_mul, hw1, one_mul]
    have hc : conj (w * z) = conj w * conj z := map_mul _ _ _
    simp only [fjChi, fjW]
    rw [hn, hc, mul_pow, mul_pow]
    linear_combination ((if ‖z‖ ≤ (N : ℝ) then (1 : ℂ) else 0) *
      (z ^ a * conj z ^ b * (Real.exp (-‖z‖ ^ 2) : ℂ))) * hwab
  have h := integral_comp_mul_of_norm_eq_one
    (fun z => fjChi N z * fjW a b z) w hw1
  have h2 : ∫ z : ℂ, fjChi N (w * z) * fjW a b (w * z) =
      -∫ z : ℂ, fjChi N z * fjW a b z := by
    simp_rw [hpt]
    exact integral_neg _
  have h3 : (∫ z : ℂ, fjChi N z * fjW a b z) =
      -∫ z : ℂ, fjChi N z * fjW a b z := h.symm.trans h2
  linear_combination h3 / 2

def fjChiP {κ : Type} [Fintype κ] (N : ℕ) (u : κ → ℂ) : ℂ := ∏ x, fjChi N (u x)

theorem measurable_productCutoff {κ : Type} [Fintype κ] (N : ℕ) : Measurable (fjChiP (κ := κ) N) := by
  show Measurable fun u : κ → ℂ => ∏ x, fjChi N (u x)
  exact Finset.measurable_prod _ fun x _ =>
    (fjChi_measurable N).comp (measurable_pi_apply x)

theorem norm_productCutoff_le_one {κ : Type} [Fintype κ] (N : ℕ) (u : κ → ℂ) : ‖fjChiP N u‖ ≤ 1 := by
  rw [fjChiP, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun x _ => fjChi_norm_le N (u x)

theorem productCutoff_eventually_eq_one {κ : Type} [Fintype κ] (u : κ → ℂ) :
    ∀ᶠ N : ℕ in atTop, fjChiP N u = 1 := by
  obtain ⟨M, hM⟩ := exists_nat_ge (∑ x, ‖u x‖)
  filter_upwards [Filter.eventually_ge_atTop M] with N hN
  unfold fjChiP
  refine Finset.prod_eq_one fun x _ => ?_
  have hx : ‖u x‖ ≤ (N : ℝ) := by
    calc ‖u x‖ ≤ ∑ y, ‖u y‖ :=
          Finset.single_le_sum (fun y _ => norm_nonneg (u y)) (Finset.mem_univ x)
      _ ≤ M := hM
      _ ≤ N := by exact_mod_cast hN
  simp [fjChi, hx]

theorem fjCut {κ : Type} [Fintype κ] (G : (κ → ℂ) → ℂ) (hG : Integrable G) :
    Tendsto (fun N : ℕ => ∫ u, fjChiP N u * G u) atTop (𝓝 (∫ u, G u)) := by
  refine tendsto_integral_of_dominated_convergence (fun u => ‖G u‖)
    (fun N => (measurable_productCutoff N).aestronglyMeasurable.mul hG.aestronglyMeasurable)
    hG.norm (fun N => Filter.Eventually.of_forall fun u => ?_)
    (Filter.Eventually.of_forall fun u => ?_)
  · show ‖fjChiP N u * G u‖ ≤ ‖G u‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_productCutoff_le_one N u)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [productCutoff_eventually_eq_one u] with N hN
    rw [hN, one_mul]

theorem fjProd {κ : Type} [Fintype κ] (a b : κ → ℕ) (u : κ → ℂ) :
    mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ) = ∏ x, fjW (a x) (b x) (u x) := by
  simp only [mono, cj, nsq, fjW, ← Finset.sum_neg_distrib,
    Real.exp_sum, Complex.ofReal_prod, Finset.prod_mul_distrib]

theorem fjProd_integrable {κ : Type} [Fintype κ] (a b : κ → ℕ) :
    Integrable (fun u : κ → ℂ => mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) := by
  simp_rw [fjProd]
  exact Integrable.fintype_prod (f := fun x (z : ℂ) => fjW (a x) (b x) z)
    fun x => fjW_integrable _ _

theorem fjProd_diag {κ : Type} [Fintype κ] (e : κ → ℕ) :
    ∫ u : κ → ℂ, mono u e * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) =
      (π : ℂ) ^ Fintype.card κ * (mfact e : ℂ) := by
  simp_rw [fjProd]
  rw [show (∫ u : κ → ℂ, ∏ x, fjW (e x) (e x) (u x)) =
      ∏ x, ∫ z : ℂ, fjW (e x) (e x) z from
    integral_fintype_prod_volume_eq_prod (fun x (z : ℂ) => fjW (e x) (e x) z)]
  simp_rw [fjW_diag]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mfact,
    Nat.cast_prod]

theorem fjProd_orth {κ : Type} [Fintype κ] (N : ℕ) (a b : κ → ℕ) (hab : a ≠ b) :
    ∫ u : κ → ℂ, fjChiP N u * (mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) = 0 := by
  have h : ∀ u : κ → ℂ, fjChiP N u *
      (mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) =
      ∏ x, (fjChi N (u x) * fjW (a x) (b x) (u x)) := by
    intro u
    rw [fjProd, fjChiP, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [show (∫ u : κ → ℂ, ∏ x, (fjChi N (u x) * fjW (a x) (b x) (u x))) =
      ∏ x, ∫ z : ℂ, fjChi N z * fjW (a x) (b x) z from
    integral_fintype_prod_volume_eq_prod
      (fun x (z : ℂ) => fjChi N z * fjW (a x) (b x) z)]
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hab
  exact Finset.prod_eq_zero (Finset.mem_univ x)
    (fjOrth N _ _ hx)

theorem fjMono_cut {κ : Type} [Fintype κ] (N : ℕ) (a : κ → ℕ) (u : κ → ℂ) :
    ‖fjChiP N u * mono u a‖ ≤ ‖mono (fun _ : κ => (N : ℂ)) a‖ := by
  simp only [fjChiP, mono, ← Finset.prod_mul_distrib, norm_prod]
  refine Finset.prod_le_prod (fun x _ => norm_nonneg _) fun x _ => ?_
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  unfold fjChi
  split_ifs with h
  · rw [norm_one, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h _
  · rw [norm_zero, zero_mul]
    positivity

private theorem continuous_nsq' {κ : Type} [Fintype κ] :
    Continuous fun u : κ → ℂ => nsq u := by
  show Continuous fun u : κ → ℂ => ∑ x, ‖u x‖ ^ 2
  exact continuous_finsetSum _ fun x _ => (continuous_norm.comp (continuous_apply x)).pow 2

private theorem continuous_exp_neg_nsq {κ : Type} [Fintype κ] :
    Continuous fun u : κ → ℂ => (Real.exp (-(nsq u)) : ℂ) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_nsq'.neg)

private theorem continuous_mono_cj {κ : Type} [Fintype κ] (e : κ → ℕ) :
    Continuous fun u : κ → ℂ => mono (cj u) e := by
  show Continuous fun u : κ → ℂ => ∏ x, conj (u x) ^ e x
  exact continuous_finsetProd _ fun x _ => (Complex.continuous_conj.comp (continuous_apply x)).pow _

theorem fjIntegrable {κ : Type} [Fintype κ] (F : (κ → ℂ) → ℂ) (S : ℝ) (hF : Continuous F)
    (hg : ∀ u, ‖F u‖ ≤ S * Real.exp (nsq u / 2)) (e : κ → ℕ) :
    Integrable (fun u : κ → ℂ => F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by
  have hbd : Integrable (fun u : κ → ℂ =>
      S * ∏ x, (‖u x‖ ^ e x * Real.exp (-(1 / 2) * ‖u x‖ ^ 2))) :=
    (Integrable.fintype_prod (f := fun x (z : ℂ) => ‖z‖ ^ e x * Real.exp (-(1 / 2) * ‖z‖ ^ 2))
      fun x => (fjMoment (1 / 2) (by norm_num) (e x)).1).const_mul S
  refine hbd.mono' ((hF.mul (continuous_mono_cj e)).mul
    continuous_exp_neg_nsq).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  show ‖F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖ ≤
    S * ∏ x, (‖u x‖ ^ e x * Real.exp (-(1 / 2) * ‖u x‖ ^ 2))
  have hprod : ∏ x, (‖u x‖ ^ e x * Real.exp (-(1 / 2) * ‖u x‖ ^ 2)) =
      (∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u / 2)) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
    unfold nsq
    congr 2
    ring
  have hnorm : ‖F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖ =
      ‖F u‖ * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u))) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_assoc]
    congr 2
    simp only [mono, cj, norm_prod, norm_pow, Complex.norm_conj]
  have hP : 0 ≤ (∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u)) :=
    mul_nonneg (Finset.prod_nonneg fun x _ => pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hexp : Real.exp (-(nsq u / 2)) =
      Real.exp (nsq u / 2) * Real.exp (-(nsq u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hnorm, hprod]
  calc ‖F u‖ * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u)))
      ≤ S * Real.exp (nsq u / 2) * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u))) :=
        mul_le_mul_of_nonneg_right (hg u) hP
    _ = S * ((∏ x, ‖u x‖ ^ e x) * Real.exp (-(nsq u / 2))) := by
        rw [hexp]
        ring

private theorem nsq_nonneg_gaussian_shift_bounds {κ : Type} [Fintype κ] (u : κ → ℂ) : 0 ≤ nsq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem continuous_mono' {κ : Type} [Fintype κ] (e : κ → ℕ) :
    Continuous fun u : κ → ℂ => mono u e := by
  show Continuous fun u : κ → ℂ => ∏ x, u x ^ e x
  exact continuous_finsetProd _ fun x _ => (continuous_apply x).pow _

theorem fjPolydisc {κ : Type} [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ)
    (hs : ∀ u, HasSum (fun e => c e * mono u e) (F u)) (e : κ → ℕ) (N : ℕ) :
    ∫ u : κ → ℂ, fjChiP N u * (F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) =
      c e * ∫ u : κ → ℂ, fjChiP N u * (mono u e * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by
  have hI : ∀ n : κ → ℕ, ∫ u : κ → ℂ, fjChiP N u *
      (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) =
      c n * ∫ u : κ → ℂ, fjChiP N u *
        (mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by
    intro n
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have h1 : Integrable fun u : κ → ℂ =>
      (1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) :=
    fjIntegrable (fun _ => 1) 1 continuous_const
      (fun u => by
        simp only [norm_one, one_mul]
        exact Real.one_le_exp (div_nonneg (nsq_nonneg_gaussian_shift_bounds u) two_pos.le)) e
  have hsN : Summable fun n : κ → ℕ => ‖c n * mono (fun _ : κ => (N : ℂ)) n‖ :=
    summable_norm_iff.mpr (hs _).summable
  have hsum : HasSum (fun n : κ → ℕ => ∫ u : κ → ℂ, fjChiP N u *
      (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)))
      (∫ u : κ → ℂ, fjChiP N u *
        (F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ))) := by
    refine hasSum_integral_of_dominated_convergence
      (fun n u => ‖c n * mono (fun _ : κ => (N : ℂ)) n‖ *
        ‖(1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖)
      (fun n => ?_) (fun n => Filter.Eventually.of_forall fun u => ?_)
      (Filter.Eventually.of_forall fun u => hsN.mul_right _) ?_
      (Filter.Eventually.of_forall fun u => ?_)
    · exact (measurable_productCutoff N).aestronglyMeasurable.mul
        ((((continuous_const.mul (continuous_mono' n)).mul
          (continuous_mono_cj e)).mul continuous_exp_neg_nsq).aestronglyMeasurable)
    · show ‖fjChiP N u *
          (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ))‖ ≤
        ‖c n * mono (fun _ : κ => (N : ℂ)) n‖ *
          ‖(1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)‖
      have hre : fjChiP N u *
          (c n * mono u n * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) =
          c n * (fjChiP N u * mono u n) *
            ((1 : ℂ) * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) := by ring
      have hb := fjMono_cut N n u
      rw [norm_mul] at hb
      rw [hre]
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
        (by positivity)
    · simp_rw [tsum_mul_right]
      exact h1.norm.const_mul _
    · exact (((hs u).mul_right _).mul_right _).mul_left _
  rw [← hI e]
  exact hsum.unique (hasSum_single e fun n hn => (hI n).trans (by
    rw [fjProd_orth N n e hn, mul_zero]))

theorem gaussianCoeffIntegral : FockJet := by
  unfold FockJet
  intro κ _ F c S hF hs hg e
  have hint_r := fjIntegrable F S hF hg e
  refine ⟨hint_r, ?_⟩
  have h1 := fjCut _ hint_r
  have h2 := ((fjCut _
    (fjProd_integrable e e)).const_mul (c e)).congr
    fun N => (fjPolydisc F c hs e N).symm
  rw [tendsto_nhds_unique h1 h2, fjProd_diag]
  ring

end Formalism.DimensionVariation
