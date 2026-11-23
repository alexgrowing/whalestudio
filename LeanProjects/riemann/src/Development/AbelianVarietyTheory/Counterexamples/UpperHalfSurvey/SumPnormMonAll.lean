import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLtMulOfLt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiInterpInterpC
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumBoundedBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.EtaStatementHolds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology

open scoped ComplexConjugate Matrix

namespace GlobalTheory.InterpCheck.Lines

open GlobalTheory.TwoLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def wtOne (Ψ : Finset (E →+* ℂ)) : Wt Ψ 2 := fun _ => ![1, 0]

def mon {Ψ : Finset (E →+* ℂ)} (τ₁ τ₂ : Ψ) (a b : Fin 2) (x : Frame Ψ 2) : ℂ := x τ₁ a 0 * x τ₂ b 0

section
omit [NumberField E] [IsCMField E]
variable {Ψ : Finset (E →+* ℂ)} {τ₁ τ₂ : Ψ}

theorem mon_sum (x : Frame Ψ 2) :
    ‖mon τ₁ τ₂ 0 0 x‖ ^ 2 + ‖mon τ₁ τ₂ 0 1 x‖ ^ 2 + ‖mon τ₁ τ₂ 1 0 x‖ ^ 2 + ‖mon τ₁ τ₂ 1 1 x‖ ^ 2 =
      colSq x τ₁ * colSq x τ₂ := by
  simp only [mon, norm_mul, colSq]; ring

theorem mon_le (a b : Fin 2) (x : Frame Ψ 2) : ‖mon τ₁ τ₂ a b x‖ ^ 2 ≤ colSq x τ₁ * colSq x τ₂ := by
  rw [← mon_sum]
  have h1 := sq_nonneg ‖mon τ₁ τ₂ 0 0 x‖
  have h2 := sq_nonneg ‖mon τ₁ τ₂ 0 1 x‖
  have h3 := sq_nonneg ‖mon τ₁ τ₂ 1 0 x‖
  have h4 := sq_nonneg ‖mon τ₁ τ₂ 1 1 x‖
  fin_cases a <;> fin_cases b <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith

theorem mon_rmul (a c : Fin 2) (x : Frame Ψ 2) {b : Frame Ψ 2} (hb : b ∈ Bor Ψ 2) :
    mon τ₁ τ₂ a c (rmul x b) = b τ₁ 0 0 * b τ₂ 0 0 * mon τ₁ τ₂ a c x := by
  simp only [mon, right_mul_borel_first_column x hb]; ring

theorem mon_diff (a b : Fin 2) : Differentiable ℂ (mon τ₁ τ₂ a b) := by
  unfold mon; fun_prop

theorem colSq_rmul (x : Frame Ψ 2) {b : Frame Ψ 2} (hb : b ∈ Bor Ψ 2) (τ : Ψ) :
    colSq (rmul x b) τ = ‖b τ 0 0‖ ^ 2 * colSq x τ := by
  simp only [colSq, right_mul_borel_first_column x hb, norm_mul]; ring

end

variable {X : Data E 2} {τ₁ τ₂ : X.Ψ}

theorem mon_pow_mem (hG : X.Gm = 1) (hΓ : X.Γ = ⊥) (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    {la : Wt X.Ψ 2} {m : ℕ} (h0 : ∀ τ, la τ 0 = m) (h1 : ∀ τ, la τ 1 = 0) (a b : Fin 2) (c : ℝ) :
    (fun x => mon τ₁ τ₂ a b x ^ m) ∈ X.SSgt la c := by
  refine mem_SSgt hG hΓ h0 h1 ((mon_diff a b).fun_pow m) (fun x b hb => ?_) (C := 1) (fun x => ?_) c
  · rw [mon_rmul _ _ _ hb, prod_two hne hall, mul_pow]
  · rw [prod_two hne hall, one_mul, norm_pow, ← pow_mul, mul_comm m 2, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) (mon_le a b x) m

theorem mon_mem (hG : X.Gm = 1) (hΓ : X.Γ = ⊥) (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    (a b : Fin 2) (c : ℝ) : mon τ₁ τ₂ a b ∈ X.SSgt (wtOne X.Ψ) c := by
  simpa using mon_pow_mem hG hΓ hne hall (la := wtOne X.Ψ) (m := 1) (fun _ => rfl) (fun _ => rfl) a b c

theorem pnorm_one (hG : X.Gm = 1) (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) {x : Frame X.Ψ 2}
    (hx : x ∈ X.dom) (P : Frame X.Ψ 2 → ℂ) :
    X.pnorm (wtOne X.Ψ) P x ^ 2 = ‖P x‖ ^ 2 / (colSq x τ₁ * colSq x τ₂) := by
  rw [pnorm_sq hG hx (m := 1) (fun _ => rfl) (fun _ => rfl), prod_two hne hall, pow_one]

def monAll (τ₁ τ₂ : X.Ψ) : Fin 4 → Frame X.Ψ 2 → ℂ :=
  ![mon τ₁ τ₂ 0 0, mon τ₁ τ₂ 0 1, mon τ₁ τ₂ 1 0, mon τ₁ τ₂ 1 1]

theorem sum_pnorm_monAll (hG : X.Gm = 1) (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    {x : Frame X.Ψ 2} (hx : x ∈ X.dom) : ∑ k, X.pnorm (wtOne X.Ψ) (monAll τ₁ τ₂ k) x ^ 2 = 1 := by
  have h1 := colSq_pos (hx τ₁).1
  have h2 := colSq_pos (hx τ₂).1
  simp only [pnorm_one hG hne hall hx]
  rw [← Finset.sum_div, div_eq_one_iff_eq (mul_pos h1 h2).ne', ← mon_sum, Fin.sum_univ_four]
  rfl

theorem nd_eq_two (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) : nd X = 2 := by
  have h := Fintype.card_of_bijective (f := idx X) ⟨idx_injective X, idx_surjective X⟩
  rw [Fintype.card_fin] at h
  rw [← h, ← Finset.card_univ, Finset.card_eq_sum_ones, sum_two hne hall]

theorem idF_mem (hG : X.Gm = 1) (hp : X.p0 = 2) : idF X.Ψ ∈ X.dom := by
  rw [mem_dom hG hp]; intro τ; simp [det_mat, idF]

theorem swF_mem (hG : X.Gm = 1) (hp : X.p0 = 2) : swF X.Ψ ∈ X.dom := by
  rw [mem_dom hG hp]; intro τ; simp [det_mat, swF]

noncomputable def thetaIn (hG : X.Gm = 1) (hp : X.p0 = 2) (hΓ : X.Γ = ⊥) (hne : τ₁ ≠ τ₂)
    (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) : ArchInM X where
  L := wtOne X.Ψ
  de := 0
  Fp := wtOne X.Ψ
  T := 44
  i := 1
  g0 := 2
  N := 4
  c := 1 / 88
  c1 := 1
  a1 := 1
  rr := 0
  n_ge := (nd_eq_two hne hall).ge
  T_ge := by rw [nd_eq_two hne hall]; norm_num
  i_pos := le_rfl
  genus_pos := by norm_num
  c_pos := by norm_num
  frame_theta_const_pos := one_pos
  frame_theta_weight_pos := one_pos
  rr_nonneg := le_rfl
  Tcg0 := by norm_num
  rr_le := by norm_num
  w := monAll τ₁ τ₂
  w_van := fun k => by fin_cases k <;> exact mon_mem hG hΓ hne hall _ _ 0
  w_nz := fun x hx => by
    by_contra h
    push Not at h
    have := sum_pnorm_monAll hG hne hall hx
    simp [Data.pnorm, h] at this
  ph := fun _ => 0
  ph_inv := fun _ _ _ _ _ _ => rfl
  ph_nonneg := fun _ _ => le_rfl
  p1 := by
    obtain ⟨ε, hε, h⟩ := first_minimum_bounded_below hG hp
    exact ⟨1, ε, one_pos, hε, fun x hx hlt => absurd (h x hx) (not_le.2 hlt)⟩
  p2 := fun x _ => by rw [mul_zero]; positivity
  p3 := ⟨1, fun x hx => by rw [sum_pnorm_monAll hG hne hall hx]; simp⟩
  et := fun x => mon τ₁ τ₂ 0 0 x ^ 0
  genus_even := even_two
  et_sec := (mon_pow_mem hG hΓ hne hall (fun _ => by simp) (fun _ => by simp) 0 0 0).1.1.1
  et_ne := ⟨_, idF_mem hG hp, by simp⟩
  p4 := ⟨1, fun x hx => by
    rw [pnorm_sq hG hx (m := 0) (fun _ => by simp) (fun _ => by simp)]; simp⟩
  th1 := fun x => mon τ₁ τ₂ 0 0 x ^ 2
  firstTheta_vanishes := mon_pow_mem hG hΓ hne hall (fun _ => by simp [wtOne]) (fun _ => by simp [wtOne]) 0 0 0
  firstTheta_ne_zero := ⟨_, idF_mem hG hp, by simp [mon, idF]⟩
  th2 := fun x => mon τ₁ τ₂ 0 0 x ^ 5
  secondTheta_vanishes := mon_pow_mem hG hΓ hne hall (fun _ => by simp [wtOne, nd_eq_two hne hall])
    (fun _ => by simp [wtOne]) 0 0 0
  secondTheta_ne_zero := ⟨_, idF_mem hG hp, by simp [mon, idF]⟩
  thp := mon τ₁ τ₂ 0 0
  thp_van := mon_mem hG hΓ hne hall 0 0 0
  thp_ne := ⟨_, idF_mem hG hp, by simp [mon, idF]⟩
  ps0 := fun _ => 0
  potential_invariant := fun _ _ _ _ _ _ => rfl
  potential_smooth := fun _ _ => contDiffOn_const
  base_psi_levi_lower_bound := fun x0 _ z _ ξ => by
    rw [zero_div, zero_mul, neg_zero, leviM, RgC.leviV_const, Complex.zero_re]
  base_psi_weighted_cf := ⟨⟨0, 0, fun _ _ => by simp⟩, fun _ _ _ => ⟨0, 0, fun _ _ ξ h => (not_isIso hG ξ h).elim⟩⟩
  posL := fun x0 hx z _ ξ hξ => by
    rw [leviM_phla hG hp hne hall hx]
    simpa [wtOne] using leviCol_add_pos hall hx z hξ
  posLde := fun x0 hx z _ ξ hξ => by
    rw [leviM_phla hG hp hne hall hx]
    have := leviCol_add_pos hall hx z hξ
    simp [wtOne]
    linarith
  posF := ⟨1 / 2, by norm_num, fun t _ _ x0 hx z _ ξ => by
    rw [leviM_phla hG hp hne hall hx, leviM_phla hG hp hne hall hx]
    simp only [Pi.sub_apply, Pi.smul_apply, wtOne, kapW, nd_eq_two hne hall]
    norm_num⟩

theorem idx_cases (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) (k : Fin (nd X)) : k = idx X τ₁ ∨ k = idx X τ₂ := by
  obtain ⟨τ, rfl⟩ := idx_surjective X k
  rcases hall τ with rfl | rfl <;> simp

noncomputable def secS (τ₁ τ₂ : X.Ψ) (k : Fin (nd X)) : Frame X.Ψ 2 → ℂ :=
  if k = idx X τ₁ then mon τ₁ τ₂ 1 0 else mon τ₁ τ₂ 0 1

theorem secS_fst : secS τ₁ τ₂ (idx X τ₁) = mon τ₁ τ₂ 1 0 := if_pos rfl

theorem secS_snd (hne : τ₁ ≠ τ₂) : secS τ₁ τ₂ (idx X τ₂) = mon τ₁ τ₂ 0 1 :=
  if_neg fun h => hne (idx_injective X h).symm

theorem sum_pnorm_secS (hG : X.Gm = 1) (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    {x : Frame X.Ψ 2} (hx : x ∈ X.dom) : ∑ k, X.pnorm (wtOne X.Ψ) (secS τ₁ τ₂ k) x ^ 2 =
      (‖mon τ₁ τ₂ 1 0 x‖ ^ 2 + ‖mon τ₁ τ₂ 0 1 x‖ ^ 2) / (colSq x τ₁ * colSq x τ₂) := by
  rw [← Function.Bijective.sum_comp ⟨idx_injective X, idx_surjective X⟩, sum_two hne hall, secS_fst,
    secS_snd hne, pnorm_one hG hne hall hx, pnorm_one hG hne hall hx, add_div]

def secW (τ₁ τ₂ : X.Ψ) (x : Frame X.Ψ 2) : ℂ := mon τ₁ τ₂ 0 0 x + mon τ₁ τ₂ 1 1 x

theorem secW_le (x : Frame X.Ψ 2) : ‖secW τ₁ τ₂ x‖ ^ 2 ≤ 2 * (colSq x τ₁ * colSq x τ₂) := by
  have h : ‖secW τ₁ τ₂ x‖ ≤ ‖mon τ₁ τ₂ 0 0 x‖ + ‖mon τ₁ τ₂ 1 1 x‖ := norm_add_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← mon_sum]
  nlinarith [sq_nonneg ‖mon τ₁ τ₂ 0 1 x‖, sq_nonneg ‖mon τ₁ τ₂ 1 0 x‖,
    sq_nonneg (‖mon τ₁ τ₂ 0 0 x‖ - ‖mon τ₁ τ₂ 1 1 x‖)]

theorem le_secW (x : Frame X.Ψ 2) : colSq x τ₁ * colSq x τ₂ ≤
    2 * (‖secW τ₁ τ₂ x‖ ^ 2 + (‖mon τ₁ τ₂ 1 0 x‖ ^ 2 + ‖mon τ₁ τ₂ 0 1 x‖ ^ 2)) := by
  have h : |‖mon τ₁ τ₂ 0 0 x‖ - ‖mon τ₁ τ₂ 1 1 x‖| ≤ ‖secW τ₁ τ₂ x‖ := by
    have := abs_norm_sub_norm_le (mon τ₁ τ₂ 0 0 x) (-mon τ₁ τ₂ 1 1 x)
    rwa [norm_neg, sub_neg_eq_add] at this
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at h2
  have h3 : ‖mon τ₁ τ₂ 0 0 x‖ * ‖mon τ₁ τ₂ 1 1 x‖ = ‖mon τ₁ τ₂ 1 0 x‖ * ‖mon τ₁ τ₂ 0 1 x‖ := by
    simp only [mon, norm_mul]; ring
  rw [← mon_sum]
  nlinarith [sq_nonneg ‖secW τ₁ τ₂ x‖, sq_nonneg (‖mon τ₁ τ₂ 1 0 x‖ - ‖mon τ₁ τ₂ 0 1 x‖)]

theorem secW_mem (hG : X.Gm = 1) (hΓ : X.Γ = ⊥) (hne : τ₁ ≠ τ₂) (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂)
    (c : ℝ) : secW τ₁ τ₂ ∈ X.SSgt (wtOne X.Ψ) c := by
  refine mem_SSgt hG hΓ (m := 1) (fun _ => rfl) (fun _ => rfl) ((mon_diff 0 0).fun_add (mon_diff 1 1))
    (fun x b hb => ?_) (C := 2) (fun x => ?_) c
  · rw [mon_rmul _ _ _ hb, mon_rmul _ _ _ hb, prod_two hne hall]; ring
  · rw [prod_two hne hall, pow_one]
    exact secW_le x

def reps (X : Data E 2) : Fin 2 → Frame X.Ψ 2 := ![idF X.Ψ, swF X.Ψ]

theorem zero_iff (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) {x : Frame X.Ψ 2} (hx : x ∈ X.dom) :
    (mon τ₁ τ₂ 1 0 x = 0 ∧ mon τ₁ τ₂ 0 1 x = 0) ↔ ∃ j, ∃ b ∈ Bor X.Ψ 2, x = rmul (reps X j) b := by
  constructor
  · rintro ⟨h1, h2⟩
    have d1 := (hx τ₁).1
    have d2 := (hx τ₂).1
    rw [det_mat] at d1 d2
    rcases mul_eq_zero.1 h1 with hu | hv
    · have hu0 : x τ₁ 0 0 ≠ 0 := fun h => d1 (by rw [h, hu]; ring)
      have hv : x τ₂ 1 0 = 0 := (mul_eq_zero.1 h2).resolve_left hu0
      have hz : ∀ τ, x τ 1 0 = 0 := fun τ => by rcases hall τ with rfl | rfl <;> assumption
      refine ⟨0, x, fun τ => ⟨(hx τ).1, fun a c hac => ?_⟩, ?_⟩
      · have : a = 1 ∧ c = 0 := by revert a c; decide
        rw [this.1, this.2]; exact hz τ
      · funext τ a c
        show _ = (mat (idF X.Ψ) τ * mat x τ) a c
        fin_cases a <;> simp [Matrix.mul_apply, mat, idF]
    · have hv1 : x τ₂ 1 0 ≠ 0 := fun h => d2 (by rw [h, hv]; ring)
      have hu : x τ₁ 0 0 = 0 := (mul_eq_zero.1 h2).resolve_right hv1
      have hz : ∀ τ, x τ 0 0 = 0 := fun τ => by rcases hall τ with rfl | rfl <;> assumption
      refine ⟨1, fun τ => ![x τ 1, x τ 0], fun τ => ⟨?_, fun a c hac => ?_⟩, ?_⟩
      · have := (hx τ).1
        rw [det_mat] at this ⊢
        intro h
        apply this
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
        linear_combination -h
      · have : a = 1 ∧ c = 0 := by revert a c; decide
        rw [this.1, this.2]; exact hz τ
      · funext τ a c
        show _ = (mat (swF X.Ψ) τ * mat (fun τ => ![x τ 1, x τ 0]) τ) a c
        fin_cases a <;> simp [Matrix.mul_apply, mat, swF]
  · rintro ⟨j, b, hb, rfl⟩
    rw [mon_rmul _ _ _ hb, mon_rmul _ _ _ hb]
    fin_cases j <;> simp [reps, mon, idF, swF]

theorem det_fderiv_ne {n : ℕ} {σ : Fin n → Fin n} (hσ : Function.Surjective σ) (i j : Fin n) :
    (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => z (σ k) / (1 + z i * z j) : V n)) 0).det ≠ 0 := by
  let L : V n →L[ℂ] V n := (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k => EuclideanSpace.proj (σ k))
  have hL : ∀ z k, L z k = z (σ k) := fun _ _ => rfl
  have he : (fun z : V n => (WithLp.toLp 2 fun k => z (σ k) / (1 + z i * z j) : V n)) =
      fun z => (1 + z i * z j)⁻¹ • L z := by
    funext z; ext k; simp [hL, div_eq_inv_mul]
  have hc : DifferentiableAt ℂ (fun z : V n => (1 + z i * z j)⁻¹) 0 := by
    refine DifferentiableAt.fun_inv ?_ (by simp)
    exact (differentiableAt_const _).fun_add
      ((EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiableAt.fun_mul
        (EuclideanSpace.proj j : V n →L[ℂ] ℂ).differentiableAt)
  have hd : fderiv ℂ (fun z : V n => (1 + z i * z j)⁻¹ • L z) 0 = L := by
    rw [(hc.hasFDerivAt.fun_smul L.hasFDerivAt).fderiv]
    ext v k
    simp
  rw [he, hd, ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot']
  intro v hv
  ext k
  obtain ⟨k', rfl⟩ := hσ k
  have : L v k' = 0 := by rw [show L v = 0 from hv]; rfl
  exact this

noncomputable def flatIn (hG : X.Gm = 1) (hp : X.p0 = 2) (hΓ : X.Γ = ⊥) (hne : τ₁ ≠ τ₂)
    (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) : FlatM X (thetaIn hG hp hΓ hne hall) where
  w0 := secW τ₁ τ₂
  s := secS τ₁ τ₂
  weightForm_vanishes := secW_mem hG hΓ hne hall 0
  s_van := fun k => by
    unfold secS
    split_ifs <;> exact mon_mem hG hΓ hne hall _ _ 0
  δ := 2
  xs := reps X
  xs_mem := fun j => by
    fin_cases j
    · exact idF_mem hG hp
    · exact swF_mem hG hp
  S_eq := fun x hx => by
    have h1 : (∀ k, secS τ₁ τ₂ k x = 0) ↔ (mon τ₁ τ₂ 1 0 x = 0 ∧ mon τ₁ τ₂ 0 1 x = 0) := by
      rw [← secS_fst, ← secS_snd hne]
      exact ⟨fun h => ⟨h _, h _⟩, fun h k => by
        rcases idx_cases hall k with rfl | rfl
        exacts [h.1, h.2]⟩
    rw [h1, zero_iff hall hx]
    simp [hΓ, lact_one']
  xs_inj := fun j j' γ hγ b hb h => by
    rw [hΓ, Subgroup.mem_bot] at hγ
    rw [hγ, lact_one'] at h
    have h0 := congrFun (congrFun (congrFun h τ₁) 0) 0
    have h1 := congrFun (congrFun (congrFun h τ₁) 1) 0
    rw [right_mul_borel_first_column _ hb] at h0 h1
    fin_cases j <;> fin_cases j' <;> simp [reps, idF, swF] at h0 h1 ⊢
  w0_ne := fun j => by
    fin_cases j <;> simp [reps, secW, mon, idF, swF]
  coord := fun j => by
    have hi : idx X τ₂ ≠ idx X τ₁ := fun h => hne (idx_injective X h).symm
    fin_cases j
    · have := det_fderiv_ne (σ := id) Function.surjective_id (idx X τ₁) (idx X τ₂)
      convert this using 6 with z k
      · rcases idx_cases hall k with rfl | rfl
        · simp [secS_fst, mon, compact_frame_first_column, reps, idF, secW]
        · simp [secS_snd hne, mon, compact_frame_first_column, reps, idF, secW]
    · have hσ : Function.Surjective fun k : Fin (nd X) =>
          if k = idx X τ₁ then idx X τ₂ else idx X τ₁ := fun k => by
        rcases idx_cases hall k with rfl | rfl
        · exact ⟨idx X τ₂, if_neg hi⟩
        · exact ⟨idx X τ₁, if_pos rfl⟩
      have := det_fderiv_ne hσ (idx X τ₁) (idx X τ₂)
      convert this using 6 with z k
      · rcases idx_cases hall k with rfl | rfl
        · simp [secS_fst, mon, compact_frame_first_column, reps, swF, secW, add_comm]
        · simp [secS_snd hne, mon, compact_frame_first_column, reps, swF, secW, hi, add_comm]
  w_le := ⟨2, fun x hx => by
    have hN := mul_pos (colSq_pos (hx τ₁).1) (colSq_pos (hx τ₂).1)
    refine (sum_pnorm_monAll hG hne hall hx).trans_le ?_
    show 1 ≤ 2 * (X.pnorm (wtOne X.Ψ) _ x ^ 2 + ∑ k, X.pnorm (wtOne X.Ψ) (secS τ₁ τ₂ k) x ^ 2)
    rw [sum_pnorm_secS hG hne hall hx, pnorm_one hG hne hall hx, ← add_div, ← mul_div_assoc,
      one_le_div hN]
    exact le_secW x⟩
  denom_le_family := ⟨2, fun x hx => by
    have hN := mul_pos (colSq_pos (hx τ₁).1) (colSq_pos (hx τ₂).1)
    show X.pnorm (wtOne X.Ψ) _ x ^ 2 ≤ 2 * ∑ k, X.pnorm (wtOne X.Ψ) (monAll τ₁ τ₂ k) x ^ 2
    rw [sum_pnorm_monAll hG hne hall hx, pnorm_one hG hne hall hx, mul_one, div_le_iff₀ hN]
    exact secW_le x⟩
  s_le_w := ⟨1, fun x hx => by
    have hN := mul_pos (colSq_pos (hx τ₁).1) (colSq_pos (hx τ₂).1)
    show ∑ k, X.pnorm (wtOne X.Ψ) (secS τ₁ τ₂ k) x ^ 2 ≤
      1 * ∑ k, X.pnorm (wtOne X.Ψ) (monAll τ₁ τ₂ k) x ^ 2
    rw [sum_pnorm_monAll hG hne hall hx, sum_pnorm_secS hG hne hall hx, mul_one, div_le_one hN,
      ← mon_sum]
    nlinarith [sq_nonneg ‖mon τ₁ τ₂ 0 0 x‖, sq_nonneg ‖mon τ₁ τ₂ 1 1 x‖]⟩
  family_le_coords := fun U hU hxs hsat => by
    have hsat' : ∀ x ∈ U, ∀ b ∈ Bor X.Ψ 2, rmul x b ∈ U := fun x hx b hb => by
      simpa [lact_one'] using hsat x hx 1 X.Γ.one_mem b hb
    let f : Frame X.Ψ 2 → ℝ := fun x =>
      (‖mon τ₁ τ₂ 1 0 x‖ ^ 2 + ‖mon τ₁ τ₂ 0 1 x‖ ^ 2) / (colSq x τ₁ * colSq x τ₂)
    have hK : IsCompact ({x : Frame X.Ψ 2 | IsOrth X x} \ U) := (isCompact_orth hG hp).diff hU
    have hsub : ∀ x ∈ {x : Frame X.Ψ 2 | IsOrth X x} \ U, x ∈ X.dom := fun x hx =>
      IW.orth_mem_dom X x hx.1
    have hf : ContinuousOn f ({x : Frame X.Ψ 2 | IsOrth X x} \ U) := by
      refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) fun x hx =>
        (mul_pos (colSq_pos (hsub x hx τ₁).1) (colSq_pos (hsub x hx τ₂).1)).ne'
      · unfold mon; fun_prop
      · unfold colSq; fun_prop
    have hpos : ∀ x ∈ {x : Frame X.Ψ 2 | IsOrth X x} \ U, 0 < f x := fun x hx => by
      refine div_pos ?_ (mul_pos (colSq_pos (hsub x hx τ₁).1) (colSq_pos (hsub x hx τ₂).1))
      by_contra hn
      have h1 : mon τ₁ τ₂ 1 0 x = 0 := by
        rw [← norm_eq_zero]; nlinarith [sq_nonneg ‖mon τ₁ τ₂ 1 0 x‖, sq_nonneg ‖mon τ₁ τ₂ 0 1 x‖]
      have h2 : mon τ₁ τ₂ 0 1 x = 0 := by
        rw [← norm_eq_zero]; nlinarith [sq_nonneg ‖mon τ₁ τ₂ 1 0 x‖, sq_nonneg ‖mon τ₁ τ₂ 0 1 x‖]
      obtain ⟨j, b, hb, he⟩ := (zero_iff hall (hsub x hx)).1 ⟨h1, h2⟩
      exact hx.2 (he ▸ hsat' _ (hxs j) b hb)
    obtain ⟨ε, hε, hle⟩ := hK.exists_forall_le' hf hpos
    refine ⟨ε⁻¹, fun x hx hxU => ?_⟩
    refine (sum_pnorm_monAll hG hne hall hx).trans_le ?_
    show 1 ≤ ε⁻¹ * ∑ k, X.pnorm (wtOne X.Ψ) (secS τ₁ τ₂ k) x ^ 2
    rw [sum_pnorm_secS hG hne hall hx, le_inv_mul_iff₀ hε, mul_one]
    obtain ⟨x1, ho, b, hb, rfl⟩ := ortho_holds 2 X x hx
    refine (hle x1 ⟨ho, fun h => hxU (hsat' _ h b hb)⟩).trans_eq ?_
    have b1 := norm_ne_zero_iff.2 (bor_ne hb τ₁)
    have b2 := norm_ne_zero_iff.2 (bor_ne hb τ₂)
    have c1 := (colSq_pos (IW.orth_mem_dom X x1 ho τ₁).1).ne'
    have c2 := (colSq_pos (IW.orth_mem_dom X x1 ho τ₂).1).ne'
    simp only [f, mon_rmul _ _ _ hb, colSq_rmul _ hb, norm_mul]
    field_simp

end GlobalTheory.InterpCheck.Lines

namespace GlobalTheory.InterpCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem leviL_nonneg (X : Data E r) (Xa : ArchInM X) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    (z : V (nd X)) (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) : 0 ≤ leviO X x0 (phla X Xa.L) z ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ, leviO, leviM, leviV]
  · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le

theorem leviRh_definite (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : leviRh X x0 z ξ = 0 := by
  have hr : ∀ w, rhF X x0 w = 0 := fun w => by
    unfold rhF
    rw [neg_eq_zero]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rcases hp with hp | hp
    · have e : (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1)) = 0 := Fin.ext hp
      rw [e]; exact IW.Lm_zero X _ τ
    · have e : (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1)) = Fin.last r := Fin.ext hp
      rw [e]; exact IW.Lm_last_cpt X x0 ho w τ
  simp only [leviRh, hr]
  rw [RgC.leviV_const, Complex.zero_re]

def Margin (X : Data E r) (Xa : ArchInM X) : Prop :=
  ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
    ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ

def MarginC (X : Data E r) (Xa : ArchInM X) : Prop :=
  ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
    ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ

theorem margins_definite (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (Xa : ArchInM X) :
    Margin X Xa ∧ MarginC X Xa := by
  constructor
  · obtain ⟨η, hη, hF⟩ := Xa.posF
    refine ⟨_, _, lt_add_one _, lt_add_one _, fun x0 ho z hz ξ => ?_⟩
    have h := hF 0 le_rfl (by rw [zero_mul]; positivity) x0 (IW.orth_mem_dom X x0 ho) z hz ξ
    rw [IW.leviM_comb X x0 ho hz] at h
    have hL := leviL_nonneg X Xa x0 ho z hz ξ
    rw [leviRh_definite X hp x0 ho, mul_zero]
    simp only [leviO, zero_mul, sub_zero] at h hL ⊢
    nlinarith [mul_nonneg hη.le hL]
  · obtain ⟨η, hη, hF⟩ := EtaStatement_holds r X Xa
    refine ⟨_, _, lt_add_one _, lt_add_one _, fun x0 ho z hz ξ => ?_⟩
    have h := hF x0 ho z hz ξ
    have hx0 := IW.orth_mem_dom X x0 ho
    have hca : ContDiffAt ℝ 2 (fun w => Xa.ps0 (cpt X x0 w)) z :=
      ((Xa.potential_smooth x0 hx0).contDiffAt ((ExF.isOpen_OmF X x0).mem_nhds hz)).of_le
        (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from WithTop.coe_le_coe.2 le_top)
    rw [IC.leviO_smul X x0 Xa.ps0 _ hca ξ] at h
    have hL := leviL_nonneg X Xa x0 ho z hz ξ
    rw [leviRh_definite X hp x0 ho, mul_zero]
    nlinarith [mul_nonneg hη.le hL]

open GlobalTheory.TwoLines Lines in

theorem model (h : Module.finrank ℚ E = 4) :
    ∃ (X : Data E 2) (Xa : ArchInM X) (Fl : FlatM X Xa), Fl.δ = 2 ∧ PropDisc X ∧ Margin X Xa ∧ MarginC X Xa ∧
      (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) ∧ (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) ∧
      ModeHalfStatement X ∧
      ∃ F ∈ X.SSgt Xa.Fp Xa.c1, ∃ j j', F (Fl.xs j) = 1 ∧ F (Fl.xs j') = 0 := by
  obtain ⟨τ₁, τ₂, hne, hall⟩ := exists_two (defData E) h
  let Xa : ArchInM (defData E) := thetaIn rfl rfl rfl hne hall
  let Fl : FlatM (defData E) Xa := flatIn rfl rfl rfl hne hall
  have hPD : PropDisc (defData E) := ClosedDiscontinuity.propDisc_closed 2 _
  obtain ⟨h1, h2⟩ := margins_definite (defData E) (Or.inr rfl) Xa
  have h3 : ∃ C : ℝ, ∀ x ∈ (defData E).dom, Xa.ps0 x ≤ C := ⟨0, fun _ _ => le_rfl⟩
  have h4 : ∀ P, (defData E).IsBddSec Xa.Fp P → P ∈ (defData E).SS Xa.Fp :=
    fun P hP => ⟨hP, fun ξ hξ => (not_isIso rfl ξ hξ).elim⟩
  have h5 := ClosedModes.modeHalf_closed 2 (defData E)
  obtain ⟨F, hF, hv⟩ := InterpolationClosed.interpC 2 (defData E) Xa Fl hPD h2 (leviL_nonneg _ Xa) h3 h4 h5
    (![1, 0] : Fin 2 → ℂ)
  exact ⟨defData E, Xa, Fl, rfl, hPD, h1, h2, h3, h4, h5, F, hF, (0 : Fin 2), (1 : Fin 2), hv _, hv _⟩

end GlobalTheory.InterpCheck
