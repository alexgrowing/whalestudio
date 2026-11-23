import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Imports

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private def gL (τ : ℝ) (p : ℕ) (i : Fin (p + 1)) : ℂ →ₗ[ℝ] ℂ :=
  if i = 0 then τ • LinearMap.id else LinearMap.id

private def fL (τ : ℝ) (p : ℕ) : (Fin (p + 1) → ℂ) →ₗ[ℝ] (Fin (p + 1) → ℂ) :=
  LinearMap.pi (fun i => (gL τ p i).comp (LinearMap.proj i))

private lemma fL_det (τ : ℝ) (p : ℕ) : LinearMap.det (fL τ p) = τ ^ 2 := by
  unfold fL
  rw [LinearMap.det_pi, Fin.prod_univ_succ]
  simp [gL, Fin.succ_ne_zero, LinearMap.det_smul, Complex.finrank_real_complex]

private def sclL (τ : ℝ) (p m : ℕ) : Xp (p + 1) m →ₗ[ℝ] Xp (p + 1) m :=
  LinearMap.prodMap (fL τ p) (LinearMap.prodMap (fL τ⁻¹ p) LinearMap.id)

private lemma sclL_apply (τ : ℝ) (p m : ℕ) (x : Xp (p + 1) m) : sclL τ p m x = scl τ x := by
  obtain ⟨a, b, c, d⟩ := x
  have h1 : fL τ p a = Function.update a 0 ((τ : ℂ) * a 0) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [fL, gL, Complex.real_smul]
    · simp [fL, gL, hi, Function.update_apply]
  have h2 : fL τ⁻¹ p b = Function.update b 0 (b 0 / (τ : ℂ)) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [fL, gL, Complex.real_smul, div_eq_inv_mul]
    · simp [fL, gL, hi, Function.update_apply]
  simp [sclL, scl, h1, h2]

theorem scl_mp {p m : ℕ} (τ : ℝ) (hτ : τ ≠ 0) :
    MeasurePreserving (scl (p := p) (m := m) τ) volume volume := by
  have hdet : LinearMap.det (sclL τ p m) = 1 := by
    unfold sclL
    rw [LinearMap.det_prodMap, LinearMap.det_prodMap, fL_det, fL_det, LinearMap.det_id, mul_one,
      inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hτ)]
  have hf : (scl (p := p) (m := m) τ) = sclL τ p m := funext fun x => (sclL_apply τ p m x).symm
  rw [hf]
  haveI : BorelSpace ((Fin m → ℂ) × ℝ) := Prod.borelSpace
  haveI : BorelSpace ((Fin (p + 1) → ℂ) × (Fin m → ℂ) × ℝ) := Prod.borelSpace
  haveI : BorelSpace (Xp (p + 1) m) := Prod.borelSpace
  haveI hp1 : (volume : Measure (Fin (p + 1) → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => volume).IsAddHaarMeasure
    infer_instance
  haveI hm1 : (volume : Measure (Fin m → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => volume).IsAddHaarMeasure
    infer_instance
  haveI : (volume : Measure ((Fin m → ℂ) × ℝ)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin m → ℂ)).prod (volume : Measure ℝ)).IsAddHaarMeasure
    infer_instance
  haveI : (volume : Measure ((Fin (p + 1) → ℂ) × (Fin m → ℂ) × ℝ)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin (p + 1) → ℂ)).prod
      (volume : Measure ((Fin m → ℂ) × ℝ))).IsAddHaarMeasure
    exact Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (Xp (p + 1) m)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin (p + 1) → ℂ)).prod
      (volume : Measure ((Fin (p + 1) → ℂ) × (Fin m → ℂ) × ℝ))).IsAddHaarMeasure
    exact Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(sclL τ p m).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [hdet]; norm_num), hdet]
  simp

theorem scl_meas {p m : ℕ} : Measurable (fun q : ℝ × Xp (p + 1) m => scl q.1 q.2) := by
  have h1 : Measurable (fun q : ℝ × Xp (p + 1) m =>
      Function.update q.2.1 0 ((q.1 : ℂ) * q.2.1 0)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases hi : i = 0
    · subst hi
      simp only [Function.update_apply, if_true]
      fun_prop
    · simp only [Function.update_apply, hi, if_false]
      fun_prop
  have h2 : Measurable (fun q : ℝ × Xp (p + 1) m =>
      Function.update q.2.2.1 0 (q.2.2.1 0 / (q.1 : ℂ))) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases hi : i = 0
    · subst hi
      simp only [Function.update_apply, if_true]
      fun_prop
    · simp only [Function.update_apply, hi, if_false]
      fun_prop
  unfold scl
  fun_prop

private lemma scl_fst_norm {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (x : Xp (p + 1) m) (j : Fin (p + 1)) :
    ‖x.1 j‖ ≤ ‖(scl τ x).1 j‖ := by
  by_cases hj : j = 0
  · subst hj
    have e : (scl τ x).1 0 = (τ : ℂ) * x.1 0 := by simp [scl]
    have hτ : ‖(τ : ℂ)‖ = τ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [e, norm_mul, hτ]
    exact le_mul_of_one_le_left (norm_nonneg _) h1
  · have e : (scl τ x).1 j = x.1 j := by simp [scl, hj]
    rw [e]

private lemma scl_snd_sq {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) (x : Xp (p + 1) m) (j : Fin (p + 1)) :
    ‖x.2.1 j‖ ^ 2 / 4 ≤ ‖(scl τ x).2.1 j‖ ^ 2 := by
  have ha := sq_nonneg ‖x.2.1 j‖
  by_cases hj : j = 0
  · subst hj
    have hτ : ‖(τ : ℂ)‖ = τ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have e : (scl τ x).2.1 0 = x.2.1 0 / (τ : ℂ) := by simp [scl]
    rw [e, norm_div, hτ, div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ ha
    nlinarith
  · have e : (scl τ x).2.1 j = x.2.1 j := by simp [scl, hj]
    rw [e]
    linarith

private lemma Lsq_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    Lsq x l ≤ Lsq (scl τ x) l := by
  unfold Lsq
  have hs : (∑ j : Fin (p + 1), if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin (p + 1), if j.val < l.val then ‖(scl τ x).1 j‖ ^ 2 else 0 := by
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · have h := scl_fst_norm τ h1 x j
      gcongr
    · exact le_rfl
  linarith

private lemma Lsq_pos {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 < Lsq x l := by
  unfold Lsq
  have h : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

private lemma rhoSq_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := Lsq_pos x (Fin.last p)
  have h2 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h3 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

private lemma rhoSq_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    rhoSq x l / 4 ≤ rhoSq (scl τ x) l := by
  have hA := Lsq_scl τ h1 x (Fin.last (p + 1))
  have hA0 := Lsq_pos x (Fin.last (p + 1))
  have hB : (scl τ x).2.2.1 = x.2.2.1 := rfl
  have hB0 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hC : (∑ j : Fin (p + 1), (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0)) / 4 ≤
      ∑ j : Fin (p + 1), (if l.val ≤ j.val then ‖(scl τ x).2.1 j‖ ^ 2 else 0) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact scl_snd_sq τ h1 h2 x j
    · simp
  unfold rhoSq
  rw [hB]
  linarith

private lemma bco_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    bco (scl τ x) l = bco x l := by
  have e1 : (scl τ x).2.2.1 = x.2.2.1 := rfl
  have e2 : (scl τ x).2.2.2 = x.2.2.2 := rfl
  unfold bco
  rw [e1, e2]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : (scl τ x).2.1 j * star ((scl τ x).1 j) = x.2.1 j * star (x.1 j) := by
    by_cases hj : j = 0
    · subst hj
      have hτ : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
      have e3 : (scl τ x).2.1 0 = x.2.1 0 / (τ : ℂ) := by simp [scl]
      have e4 : (scl τ x).1 0 = (τ : ℂ) * x.1 0 := by simp [scl]
      rw [e3, e4, star_mul', Complex.star_def, Complex.conj_ofReal]
      field_simp
    · have e3 : (scl τ x).2.1 j = x.2.1 j := by simp [scl, hj]
      have e4 : (scl τ x).1 j = x.1 j := by simp [scl, hj]
      rw [e3, e4]
  rw [key]

theorem de_scl {p m : ℕ} (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) (x : Xp (p + 1) m) (l : Fin (p + 2)) :
    de x l / 2 ≤ de (scl τ x) l := by
  unfold de
  rw [bco_scl τ h1 x l]
  have hL := Lsq_scl τ h1 x l
  have hL0 := Lsq_pos x l
  have hr := rhoSq_scl τ h1 h2 x l
  have hr0 := rhoSq_nonneg x l
  have hb := sq_nonneg ‖bco x l‖
  have hm : Lsq x l * (rhoSq x l / 4) ≤ Lsq (scl τ x) l * rhoSq (scl τ x) l :=
    mul_le_mul hL hr (by positivity) (by linarith)
  have key : (Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2) / 4 ≤
      Lsq (scl τ x) l * rhoSq (scl τ x) l + ‖bco x l‖ ^ 2 := by
    nlinarith
  have h4 : Real.sqrt ((Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2) / 4) =
      Real.sqrt (Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2) / 2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt key

private lemma linF_scl {p m : ℕ} (τ : ℝ) (hτ : τ ≠ 0) (η η' : Fin (p + 1) → ℂ) (ζ : Fin m → ℂ)
    (x : Xp (p + 1) m) :
    (τ : ℂ) * linF η η' ζ (scl τ x) = x.2.1 0 * η' 0 +
      ((∑ j : Fin p, (x.1 j.succ * η j.succ + x.2.1 j.succ * η' j.succ)) + ∑ i, x.2.2.1 i * ζ i) * τ +
      x.1 0 * η 0 * τ ^ 2 := by
  have hτ' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  have e1 : (scl τ x).1 0 = (τ : ℂ) * x.1 0 := by simp [scl]
  have e2 : (scl τ x).2.1 0 = x.2.1 0 / (τ : ℂ) := by simp [scl]
  have e3 : ∀ j : Fin p, (scl τ x).1 j.succ = x.1 j.succ := fun j => by
    simp [scl, Fin.succ_ne_zero]
  have e4 : ∀ j : Fin p, (scl τ x).2.1 j.succ = x.2.1 j.succ := fun j => by
    simp [scl, Fin.succ_ne_zero]
  have e5 : (scl τ x).2.2.1 = x.2.2.1 := rfl
  have hk : (τ : ℂ) * (x.2.1 0 / (τ : ℂ) * η' 0) = x.2.1 0 * η' 0 := by
    field_simp
  unfold linF
  rw [Fin.sum_univ_succ]
  simp only [e1, e2, e3, e4, e5]
  linear_combination hk

private lemma enn_norm (z : ℂ) : ENNReal.ofReal ‖z‖ = (‖z‖₊ : ℝ≥0∞) := by
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

theorem scl_weight (hS : SUB) {δ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hγ0 : 0 < γ) (hγ : γ ≤ δ / 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ {p m : ℕ} (η η' : Fin (p + 1) → ℂ) (ζ : Fin m → ℂ) (x : Xp (p + 1) m),
      ∫⁻ τ in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4)) ≤
        ENNReal.ofReal C * (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := by
  obtain ⟨CS, hCS⟩ := hS (δ / 4) (by positivity) (by linarith)
  have hC : 0 < 2 ^ (δ / 4) * (|CS| + 1) := by positivity
  refine ⟨2 ^ (δ / 4) * (|CS| + 1), hC, ?_⟩
  intro p m η η' ζ x
  have hCn : ENNReal.ofReal (2 ^ (δ / 4) * (|CS| + 1)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hC
  have hng : -γ < 0 := by linarith
  by_cases hη : η' 0 = 0
  · refine le_top.trans (le_of_eq ?_)
    rw [hη, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_neg hng, ENNReal.mul_top hCn,
      ENNReal.top_mul]
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    simp [hγ0.le]
  by_cases ha : x.2.1 0 = 0
  · refine le_top.trans (le_of_eq ?_)
    rw [ha, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_neg hng, ENNReal.mul_top]
    refine mul_ne_zero hCn ?_
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    simp [hγ0.le]
  set R : ℂ := (∑ j : Fin p, (x.1 j.succ * η j.succ + x.2.1 j.succ * η' j.succ)) + ∑ i, x.2.2.1 i * ζ i
  set c : Fin 3 → ℂ := ![x.2.1 0 * η' 0, R, x.1 0 * η 0] with hc
  have hc0 : c 0 = x.2.1 0 * η' 0 := rfl
  have hc1 : c 1 = R := rfl
  have hc2 : c 2 = x.1 0 * η 0 := rfl
  have hpt : ∀ τ ∈ Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4)) ≤
      ENNReal.ofReal (2 ^ (δ / 4)) *
        ENNReal.ofReal ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4))) := by
    intro τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hP : ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖ ≤ 2 * ‖linF η η' ζ (scl τ x)‖ := by
      rw [hc0, hc1, hc2, ← linF_scl τ hτ0.ne' η η' ζ x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hτ0]
      gcongr
      exact hτ.2
    have hF := norm_nonneg (linF η η' ζ (scl τ x))
    have hP0 := norm_nonneg (c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2)
    have h1 : (1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) / 2 ≤ 1 + ‖linF η η' ζ (scl τ x)‖ := by linarith
    calc (1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4)
        ≤ ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) / 2) ^ (-δ / 4) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      _ = 2 ^ (δ / 4) * (1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4)) := by
          rw [Real.div_rpow (by positivity) (by norm_num), neg_div,
            Real.rpow_neg (x := 2) (by norm_num), div_inv_eq_mul, mul_comm]
  have ht : 0 < ‖x.2.1 0‖ * ‖η' 0‖ := mul_pos (norm_pos_iff.2 ha) (norm_pos_iff.2 hη)
  have hct : ‖x.2.1 0‖ * ‖η' 0‖ ≤ ‖c‖ := by
    rw [← norm_mul, ← hc0]; exact norm_le_pi_norm c 0
  have e1 : (1 + ‖c‖) ^ (-(δ / 4) / 2) ≤ (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-(δ / 4) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have e2 : (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-(δ / 4) / 2) ≤ (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have e3 : (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) ≤ (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith)
  have e4 : (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) = ‖η' 0‖ ^ (-γ) * ‖x.2.1 0‖ ^ (-γ) := by
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_comm]
  have e5 : CS * (1 + ‖c‖) ^ (-(δ / 4) / 2) ≤ (|CS| + 1) * (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
    calc CS * (1 + ‖c‖) ^ (-(δ / 4) / 2) ≤ (|CS| + 1) * (1 + ‖c‖) ^ (-(δ / 4) / 2) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self CS]) (by positivity)
      _ ≤ (|CS| + 1) * (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
          mul_le_mul_of_nonneg_left (e1.trans (e2.trans e3)) (by positivity)
  calc ∫⁻ τ in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4))
      ≤ ∫⁻ τ in Icc (1 : ℝ) 2, ENNReal.ofReal (2 ^ (δ / 4)) *
          ENNReal.ofReal ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4))) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (2 ^ (δ / 4)) * ∫⁻ τ in Icc (1 : ℝ) 2,
          ENNReal.ofReal ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 ^ (δ / 4)) * ENNReal.ofReal (CS * (1 + ‖c‖) ^ (-(δ / 4) / 2)) := by
        gcongr; exact hCS c
    _ = ENNReal.ofReal (2 ^ (δ / 4) * (CS * (1 + ‖c‖) ^ (-(δ / 4) / 2))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (2 ^ (δ / 4) * (|CS| + 1) * ‖η' 0‖ ^ (-γ) * ‖x.2.1 0‖ ^ (-γ)) := by
        apply ENNReal.ofReal_le_ofReal
        calc 2 ^ (δ / 4) * (CS * (1 + ‖c‖) ^ (-(δ / 4) / 2))
            ≤ 2 ^ (δ / 4) * ((|CS| + 1) * (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ)) :=
              mul_le_mul_of_nonneg_left e5 (by positivity)
          _ = 2 ^ (δ / 4) * (|CS| + 1) * ‖η' 0‖ ^ (-γ) * ‖x.2.1 0‖ ^ (-γ) := by rw [e4]; ring
    _ = ENNReal.ofReal (2 ^ (δ / 4) * (|CS| + 1)) * (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) *
          (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hη),
          ← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 ha), enn_norm, enn_norm]

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
