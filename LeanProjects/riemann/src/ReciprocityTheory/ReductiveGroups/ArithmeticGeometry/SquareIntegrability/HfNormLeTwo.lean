import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CardChoiceLe

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

section Core

variable {E : Type} [Field E] [NumberField E]

theorem Hf_norm_le_two {dim : (E →+* ℂ) → ℕ} (e y : Vsp dim) (he : ‖e‖ = 1) (hy : ‖y‖ ≤ 2) :
    ‖Hf e y‖ ≤ 2 := by
  rw [Hf_eq_inner']
  calc ‖inner ℂ y e‖ ≤ ‖y‖ * ‖e‖ := norm_inner_le_norm y e
    _ ≤ 2 := by rw [he, mul_one]; exact hy

open Classical in
theorem eU_props {dim : (E →+* ℂ) → ℕ} {n nb : ℕ} (bs : Fin nb → Block E n dim) (j : Fin nb)
    (a : Fin (bs j).i) : InPart (bs j).τ (eU bs j a) ∧ ‖eU bs j a‖ = 1 := by
  refine ⟨fun k hk => ?_, by simp [eU]⟩
  simp only [eU, PiLp.single_apply]
  rw [if_neg]
  rintro rfl
  exact hk rfl

theorem norm_sgnT {dim : (E →+* ℂ) → ℕ} {n nb : ℕ} (bs : Fin nb → Block E n dim) (T : Choice bs) :
    ‖sgnT bs T‖ ≤ 1 := by
  unfold sgnT
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun r _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign (T j r)) with h | h <;> simp [h]

set_option maxHeartbeats 1000000 in
open Classical in
theorem jof_core (hx : Ext.All) (hs : SplitStatement) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (he : ColEmptyStatement) [IsCMField E] (X : PT E) {n nb : ℕ}
    (bs : Fin nb → Block E n X.dim) (hD : Disj bs) (P : Par X (DF bs)) :
    ∃ F ∈ X.Sec P.q n, X.l2 P.q F = 1 ∧ P.Jbound n ≤ ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 := by
  obtain ⟨I, hI⟩ := hs E X (DF bs) P
  choose yB sB μB hsB hbd hl2 hyB hdet hμ using block_data_all X bs hx hc ht ha P I hI
  obtain ⟨se, hse, hse0, hsel⟩ := he E X (DF bs) P I hI
  set y : (Σ j : Fin nb, Fin (bs j).i) → Vsp X.dim := fun p => yB p.1 p.2 with hydef
  set μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ := fun p => μB p.1 p.2 with hμdef
  set sc : Fin n → (Fin 1 → Vsp X.dim) → ℂ := fun k =>
    match owner bs k with
    | some p => sB p.1 p.2
    | none => se with hscdef
  have hsc_col : ∀ p, sc (colB bs p) = sB p.1 p.2 := fun p => by
    simp only [hscdef, owner_colB hD p]
  have hsc_none : ∀ k, owner bs k = none → sc k = se := fun k hk => by
    simp only [hscdef, hk]
  have hsc : ∀ k, sc k ∈ X.Sec P.q 1 := by
    intro k
    rcases hk : owner bs k with _ | p
    · rw [hsc_none k hk]; exact hse
    · rw [← colB_of_owner hk, hsc_col]; exact hsB _ _
  have hcd : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (sc k) := fun k => sec_contDiff X (hsc k)
  set F₀ := tens X sc with hF₀def
  have hF₀ : F₀ ∈ X.Sec P.q n := tens_mem X hsc
  set V0 := polyDeriv (P1 bs) dir F₀ 0 with hV0def
  have hV0 := polyDeriv_determinantPoly_tensor X bs sc hcd
  set ε := P.eps1 with hεdef
  set ee : Fin n → ℂ := fun _ => se 0 with heedef
  set A := idealA bs μ y ee with hAdef
  set D : Choice bs → Fin n → ℂ := fun T k =>
    d1 (sc k) (colL (lst X bs T) k).length (fun j => (colL (lst X bs T) k).get j) with hDdef
  set α : Fin n → ℝ := fun k =>
    match owner bs k with
    | some p => ‖μ p‖ * 2 ^ (bs p.1).c
    | none => ‖se 0‖ with hαdef
  set δ : Fin n → ℝ := fun k =>
    match owner bs k with
    | some p => ε * ‖μ p‖
    | none => 0 with hδdef
  have hε0 : 0 ≤ ε := by
    rw [hεdef, Par.eps1]; positivity

  have hAb : ∀ T k, ‖A T k‖ ≤ α k := by
    intro T k
    rcases hk : owner bs k with _ | p
    · simp only [hAdef, idealA, hk, hαdef, heedef, le_refl]
    · simp only [hAdef, idealA, hk, hαdef]
      rw [norm_mul, norm_prod]
      gcongr
      calc ∏ r, ‖Hf (eU bs p.1 (T p.1 r p.2)) (y p)‖ ≤ ∏ _r : Fin (bs p.1).c, (2 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun r _ =>
              Hf_norm_le_two _ _ (eU_props bs p.1 _).2 (hyB p.1 p.2)
        _ = 2 ^ (bs p.1).c := by simp
  have hDb : ∀ T k, ‖D T k - A T k‖ ≤ δ k := by
    intro T k
    rcases hk : owner bs k with _ | p
    · simp only [hAdef, idealA, hk, hδdef, hDdef, heedef]
      rw [colL_empty X hD T hk, hsc_none k hk]
      simp [d1_zero]
    · have hkp := colB_of_owner hk
      subst hkp
      simp only [hAdef, idealA, hk, hδdef, hDdef]
      rw [hsc_col]
      exact iteratedDeriv_list_bound (sB p.1 p.2) (bs p.1).c (μ p) (y p) (ε * ‖μ p‖) (bs p.1).τ
        (hbd p.1 p.2) _ (fun r => eU bs p.1 (T p.1 r p.2)) (colL_block X hD T p)
        (fun r => eU_props bs p.1 _)
  have herr := norm_sum_prod_sub_le (sgnT bs) (norm_sgnT bs) D A α δ hAb hDb
  rw [main_term bs hD μ y ee] at herr
  have hV0e : V0 = ∑ T, sgnT bs T * ∏ k, D T k := hV0
  rw [← hV0e] at herr
  set N := Fintype.card (Choice bs) with hNdef

  set Ce : ℝ := ∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ‖se 0‖ with hCedef
  set Mμ : ℝ := ∏ p, ‖μ p‖ with hMμdef
  set Dt : ℝ := ∏ j, ‖(blockM bs y j).det‖ ^ (bs j).c with hDtdef
  set A1 : ℝ := ∏ p : (Σ j : Fin nb, Fin (bs j).i), ((2 : ℝ) ^ (bs p.1).c + ε) with hA1def
  have hCe0 : 0 ≤ Ce := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hMμ0 : 0 ≤ Mμ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hCm : ‖(∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
      ∏ j, (blockM bs y j).det ^ (bs j).c‖ = Ce * Mμ * Dt := by
    simp only [norm_mul, norm_prod, norm_pow, hCedef, hMμdef, hDtdef, heedef]
  have hα : ∏ k, α k = Ce * (Mμ * 2 ^ DF bs) := by
    rw [prod_cols hD]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [Finset.mem_filter] at hk
      simp only [hαdef, hk.2]
    · rw [hMμdef, ← prod_two_pow bs, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [hαdef, owner_colB hD p]
  have hαδ : ∏ k, (α k + δ k) = Ce * (Mμ * A1) := by
    rw [prod_cols hD]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [Finset.mem_filter] at hk
      simp only [hαdef, hδdef, hk.2, add_zero]
    · rw [hMμdef, hA1def, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [hαdef, hδdef, owner_colB hD p]
      ring

  have hr1 : 1 ≤ X.r := by
    have := P.hfr
    rcases Nat.eq_zero_or_pos X.r with h | h
    · rw [h, mul_zero] at this; omega
    · exact h
  have hir : ∀ j, (bs j).i ≤ X.r := fun j => by
    have h1 := (bs j).hi
    have h2 := X.dim_conj (bs j).τ
    omega
  have hcard := card_choice_le bs X.r hir
  have hm := card_pos_le bs
  have hK : ε ≤ Real.exp (-(((DF bs : ℝ) + 1) * ((X.r : ℝ) * Real.log X.r + 3 * X.r + 3))) := by
    have h6 := P.C6
    rw [hεdef, Par.eps1]
    exact eps_bound X.gA (dstar (E := E) P.m) (t0 (E := E) P.q P.R0) _ (by push_cast at h6 ⊢; linarith)
  have hε1 : ε ≤ 1 := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ X.r by exact_mod_cast hr1)
    have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
    have h1 : 0 ≤ ((DF bs : ℝ) + 1) * ((X.r : ℝ) * Real.log X.r + 3 * X.r + 3) :=
      mul_nonneg (by positivity) (by have := mul_nonneg hr0 hlog; linarith)
    exact hK.trans (Real.exp_le_one_iff.2 (by linarith))
  have hnum := num_bound X.r (DF bs) hr1 ε hε0 hK
  set m := Fintype.card (Σ j : Fin nb, Fin (bs j).i) with hmdef
  have hA1le : A1 - 2 ^ DF bs ≤ 2 ^ DF bs * (m * ε * 2 ^ DF bs) := by
    have h1 : A1 ≤ 2 ^ DF bs * (1 + ε) ^ m := by
      rw [hA1def, ← prod_two_pow bs, hmdef, ← Finset.card_univ, ← Finset.prod_const,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun p _ => ?_
      have : (1 : ℝ) ≤ 2 ^ (bs p.1).c := one_le_pow₀ (by norm_num)
      nlinarith
    have h2 := one_add_pow_sub_one_le ε hε0 m
    have h3 : (1 + ε) ^ m ≤ 2 ^ DF bs :=
      (pow_le_pow_left₀ (by linarith) (by linarith) m).trans (pow_le_pow_right₀ (by norm_num) hm)
    have h4 : (0 : ℝ) ≤ 2 ^ DF bs := by positivity
    have h5 : (0 : ℝ) ≤ m * ε := by positivity
    calc A1 - 2 ^ DF bs ≤ 2 ^ DF bs * ((1 + ε) ^ m - 1) := by nlinarith
      _ ≤ 2 ^ DF bs * (m * ε * (1 + ε) ^ m) := mul_le_mul_of_nonneg_left h2 h4
      _ ≤ 2 ^ DF bs * (m * ε * 2 ^ DF bs) := by gcongr
  set δ0 : ℝ := (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 with hδ0def
  have hδ0pos : 0 < δ0 := by positivity
  have hδ01 : δ0 ≤ 1 := by
    have : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) X.r; linarith)
    rw [hδ0def]; linarith
  have hDt : δ0 ^ DF bs ≤ Dt := by
    rw [hDtdef]
    refine prod_det_ge bs _ δ0 hδ0pos.le hδ01 (fun j hj => hdet j) (fun j hj => ?_)
    haveI : IsEmpty (Fin (bs j).i) := by rw [hj]; infer_instance
    rw [Matrix.det_isEmpty, norm_one]
  have hδ0exp : Real.exp (-((X.r : ℝ) / 2 + 1)) ≤ δ0 := by
    rw [hδ0def, Real.rpow_def_of_pos (by norm_num)]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have he1 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      have := Real.add_one_le_exp (1 : ℝ)
      exact inv_anti₀ (by norm_num) (by linarith)
    have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
    calc Real.exp (-((X.r : ℝ) / 2 + 1)) = Real.exp (-((X.r : ℝ) / 2)) * Real.exp (-1) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (Real.log 2 * (-(X.r : ℝ) / 2)) * (1 / 2) := by
          gcongr
          nlinarith
      _ = Real.exp (Real.log 2 * (-(X.r : ℝ) / 2)) / 2 := by ring
  have hnum2 : (N : ℝ) * (A1 - 2 ^ DF bs) ≤ Dt / 2 := by
    have hc : (N : ℝ) ≤ (X.r : ℝ) ^ DF bs := by exact_mod_cast hcard
    have hm' : (m : ℝ) ≤ DF bs := by exact_mod_cast hm
    have hA0 : 0 ≤ A1 - 2 ^ DF bs := by
      rw [hA1def, ← prod_two_pow bs, sub_nonneg]
      exact Finset.prod_le_prod (fun _ _ => by positivity) fun p _ => le_add_of_nonneg_right hε0
    have hexp : Real.exp (-((X.r : ℝ) / 2 + 1)) ^ DF bs = Real.exp (-(((X.r : ℝ) / 2 + 1) * DF bs)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hE : 0 < Real.exp ((X.r / 2 + 1) * DF bs) := Real.exp_pos _
    have hfin : (DF bs : ℝ) * ε * (4 * X.r) ^ DF bs ≤ Real.exp (-(((X.r : ℝ) / 2 + 1) * DF bs)) / 2 := by
      rw [Real.exp_neg, ← one_div, div_div, le_div_iff₀ (by positivity)]
      calc (DF bs : ℝ) * ε * (4 * X.r) ^ DF bs * (Real.exp ((X.r / 2 + 1) * DF bs) * 2)
          = 2 * (DF bs : ℝ) * (4 * X.r) ^ DF bs * Real.exp ((X.r / 2 + 1) * DF bs) * ε := by ring
        _ ≤ 1 := hnum
    have h4r : ((4 : ℝ) * X.r) ^ DF bs = 2 ^ DF bs * 2 ^ DF bs * (X.r : ℝ) ^ DF bs := by
      rw [← mul_pow, ← mul_pow]; norm_num
    have hmε : (m : ℝ) * ε * 2 ^ DF bs ≤ (DF bs : ℝ) * ε * 2 ^ DF bs :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm' hε0) (by positivity)
    have hr0 : (0 : ℝ) ≤ (X.r : ℝ) ^ DF bs := by positivity
    have h20 : (0 : ℝ) ≤ 2 ^ DF bs := by positivity
    calc (N : ℝ) * (A1 - 2 ^ DF bs)
        ≤ (X.r : ℝ) ^ DF bs * (2 ^ DF bs * (m * ε * 2 ^ DF bs)) :=
          mul_le_mul hc hA1le hA0 hr0
      _ ≤ (X.r : ℝ) ^ DF bs * (2 ^ DF bs * (DF bs * ε * 2 ^ DF bs)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmε h20) hr0
      _ = (DF bs : ℝ) * ε * (4 * X.r) ^ DF bs := by rw [h4r]; ring
      _ ≤ Real.exp (-(((X.r : ℝ) / 2 + 1) * DF bs)) / 2 := hfin
      _ ≤ Dt / 2 := by
          rw [← hexp]
          have := pow_le_pow_left₀ (Real.exp_pos _).le hδ0exp (DF bs)
          linarith
  have herr2 : ‖V0 - (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
      ∏ j, (blockM bs y j).det ^ (bs j).c‖ ≤ Ce * Mμ * Dt / 2 := by
    refine herr.trans ?_
    rw [hαδ, hα]
    calc (N : ℝ) * (Ce * (Mμ * A1) - Ce * (Mμ * 2 ^ DF bs))
        = Ce * Mμ * ((N : ℝ) * (A1 - 2 ^ DF bs)) := by ring
      _ ≤ Ce * Mμ * (Dt / 2) := mul_le_mul_of_nonneg_left hnum2 (mul_nonneg hCe0 hMμ0)
      _ = Ce * Mμ * Dt / 2 := by ring
  have hV0ge : Ce * Mμ * Dt / 2 ≤ ‖V0‖ := by
    have := norm_sub_norm_le ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) *
      (∏ p, μ p) * ∏ j, (blockM bs y j).det ^ (bs j).c) V0
    rw [hCm, norm_sub_rev] at this
    linarith

  have hCepos : 0 < Ce := Finset.prod_pos fun _ _ => by
    have := hse0; linarith
  have hMμpos : 0 < Mμ := Finset.prod_pos fun p _ => norm_pos_iff.2 (hμ p.1 p.2)
  have hDtpos : 0 < Dt := lt_of_lt_of_le (pow_pos hδ0pos _) hDt
  have hV0pos : 0 < ‖V0‖ := lt_of_lt_of_le (by positivity) hV0ge
  have hl2F : X.l2 P.q F₀ = ∏ k, X.l2 P.q (sc k) := l2_tens_eq_prod X P.q sc
  have hl2pos : 0 < X.l2 P.q F₀ := by
    rcases (l2NormSq_nonneg_gaussianTorus X P.q F₀).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [hl2F] at h
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h.symm
      have hz := eq_zero_of_l2_eq_zero X hx.1 P.hq (hsc k) hk
      have hF0 : F₀ = 0 := by
        funext v
        rw [hF₀def, tens]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hz]; rfl)
      have : V0 = 0 := by rw [hV0def, hF0]; exact polyDeriv_zero_fun _ _ _
      rw [this, norm_zero] at hV0pos
      exact lt_irrefl 0 hV0pos

  set a : ℝ := 2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q with hadef
  have ha0 : 0 ≤ a := by
    have := Cchi_nonneg (E := E) P.m; have := ph_nonneg P; have := Real.pi_pos
    rw [hadef]; positivity
  set w : ℝ := 4⁻¹ * P.K6⁻¹ * Real.exp (-a) with hwdef
  have hK6 := inv_constant_nonneg P
  have hJ : P.Jbound n = (∏ _k : Fin n, w) * (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) := by
    have hwn : w ^ n = (4 : ℝ)⁻¹ ^ n * P.K6⁻¹ ^ n *
        Real.exp (-(2 * Real.pi * n * Cchi (E := E) P.m * P.ph / P.q)) := by
      rw [hwdef, mul_pow, mul_pow, ← Real.exp_nat_mul]
      congr 2
      rw [hadef]
      ring
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hwn, Par.Jbound, Par.K6]
    ring
  have hmain : P.Jbound n * X.l2 P.q F₀ ≤ ‖V0‖ ^ 2 := by
    have hsq : (Ce * Mμ * Dt / 2) ^ 2 ≤ ‖V0‖ ^ 2 := pow_le_pow_left₀ (by positivity) hV0ge 2
    refine le_trans ?_ hsq
    rw [hJ, hl2F, prod_cols hD (fun _ => w), prod_cols hD (fun k => X.l2 P.q (sc k))]
    have he1 : (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
        (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k)) ≤ Ce ^ 2 := by
      rw [← Finset.prod_mul_distrib, hCedef, ← Finset.prod_pow]
      refine Finset.prod_le_prod (fun k _ => mul_nonneg (by positivity) (l2NormSq_nonneg_gaussianTorus X P.q _))
        fun k hk => ?_
      rw [Finset.mem_filter] at hk
      rw [hsc_none k hk.2, hwdef]
      have h1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h2 := hsel
      have h3 : (1 : ℝ) / 4 ≤ ‖se 0‖ ^ 2 := by nlinarith
      have h4 := l2NormSq_nonneg_gaussianTorus X P.q se
      have h5 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
      nlinarith [mul_nonneg hK6 h4, mul_le_mul_of_nonneg_left h1 (mul_nonneg hK6 h4)]
    have he2 : (∏ p : (Σ j : Fin nb, Fin (bs j).i), w) *
        (∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p))) ≤ 4⁻¹ * Mμ ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      calc ∏ p : (Σ j : Fin nb, Fin (bs j).i), (w * X.l2 P.q (sc (colB bs p)))
          ≤ ∏ p : (Σ j : Fin nb, Fin (bs j).i), (4⁻¹ * ‖μ p‖ ^ 2) := by
            refine Finset.prod_le_prod (fun p _ => mul_nonneg (by positivity) (l2NormSq_nonneg_gaussianTorus X P.q _))
              fun p _ => ?_
            rw [hsc_col, hwdef]
            have := hl2 p.1 p.2
            nlinarith
        _ = (4⁻¹) ^ m * Mμ ^ 2 := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hMμdef, Finset.prod_pow]
        _ ≤ 4⁻¹ * Mμ ^ 2 := by
            have hm1 : 1 ≤ m := card_pos_pos bs P.hDF
            have : ((4 : ℝ)⁻¹) ^ m ≤ 4⁻¹ := by
              calc ((4 : ℝ)⁻¹) ^ m ≤ (4⁻¹) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
                _ = 4⁻¹ := pow_one _
            gcongr
    have he3 : (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) ≤ Dt ^ 2 := by
      have hδsq : δ0 ^ 2 = (2 : ℝ)⁻¹ ^ (X.r + 2) := by
        rw [hδ0def, div_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (-(X.r : ℝ) / 2)) 2,
          ← Real.rpow_mul (by norm_num)]
        have h2 : (-(X.r : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -(X.r : ℝ) := by push_cast; ring
        rw [h2, Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_add, inv_pow, inv_pow]
        ring
      have h1 : (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) = (δ0 ^ DF bs) ^ 2 := by
        rw [pow_mul, ← hδsq, ← pow_mul, ← pow_mul, mul_comm]
      rw [h1]
      exact pow_le_pow_left₀ (by positivity) hDt 2
    have hA : 0 ≤ (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
        (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k)) :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
        (Finset.prod_nonneg fun _ _ => l2NormSq_nonneg_gaussianTorus X P.q _)
    have hB : 0 ≤ (∏ p : (Σ j : Fin nb, Fin (bs j).i), w) *
        (∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p))) :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
        (Finset.prod_nonneg fun _ _ => l2NormSq_nonneg_gaussianTorus X P.q _)
    calc (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
          (∏ p : (Σ j : Fin nb, Fin (bs j).i), w) * (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) *
          ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k)) *
            ∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p)))
        = ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), w) *
            (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), X.l2 P.q (sc k))) *
          ((∏ p : (Σ j : Fin nb, Fin (bs j).i), w) *
            (∏ p : (Σ j : Fin nb, Fin (bs j).i), X.l2 P.q (sc (colB bs p)))) *
          (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF bs) := by ring
      _ ≤ Ce ^ 2 * (4⁻¹ * Mμ ^ 2) * Dt ^ 2 := by
          gcongr
      _ = (Ce * Mμ * Dt / 2) ^ 2 := by ring

  set c : ℂ := (((Real.sqrt (X.l2 P.q F₀))⁻¹ : ℝ) : ℂ) with hcdef
  have hsq : 0 < Real.sqrt (X.l2 P.q F₀) := Real.sqrt_pos.2 hl2pos
  refine ⟨c • F₀, Submodule.smul_mem _ _ hF₀, ?_, ?_⟩
  · rw [l2_smul, hcdef, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hsq, inv_pow,
      Real.sq_sqrt hl2pos.le, inv_mul_cancel₀ hl2pos.ne']
  · rw [polyDeriv_smul_fun _ _ (sec_contDiff X hF₀), ← hV0def, norm_mul, mul_pow, hcdef,
      Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hsq, inv_pow, Real.sq_sqrt hl2pos.le,
      inv_mul_eq_div, le_div_iff₀ hl2pos]
    exact hmain

end Core

theorem jOf (hx : Ext.All) (hs : SplitStatement) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (he : ColEmptyStatement) : JStatement := by
  intro E _ _ _ X n nb bs hD P
  exact jof_core hx hs hc ht ha he X bs hD P

end ReciprocityTheory.ChartRestriction.G.I2
