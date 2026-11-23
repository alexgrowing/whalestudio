import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PrjMemSpanC

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def Inv {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (σ : E →+* ℂ) (ρ : ℕ) (K0 Bu : ℝ)
    (k : ℕ) (χ w : ℕ → Vsp dim) (R μ : ℕ → ℝ) (ε : ℕ → ℕ → ℂ) : Prop :=
  (∀ s < k, χ s ∈ Xg L I) ∧
  (∀ s < k, w s ∈ Wk σ χ (s + 1)) ∧
  (∀ s < k, ∀ s' < k, inner ℂ (w s) (w s') = if s = s' then (1 : ℂ) else 0) ∧
  (∀ s < k, prj σ (χ s) =
    (R s : ℂ) • (w s + ∑ i ∈ Finset.range s, (starRingEnd ℂ) (ε s i) • w i)) ∧
  (∀ s < k, ∀ i, s ≤ i → ε s i = 0) ∧
  (∀ s < k, ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 ≤ (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2) ∧
  (∀ s < k, 30 * (ρ : ℝ) ^ 2 * K0 * μ s ≤ R s ∧
    ‖χ s‖ ≤ (Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1) * K0 * μ s) ∧
  (∀ s < k, 1 ≤ μ s ∧ ∀ y ∈ Xg L I, |2 * inner ℝ (χ s) y| ≤ ‖y‖ ^ 2 ∨ μ s ≤ ‖y‖) ∧
  (∀ s < k, χ s ∈ Zs L I (μ s) ∧ ∀ y ∈ Xg L I, prj σ y ∉ Wk σ χ s → μ s ≤ ‖y‖) ∧
  (∀ s < k, μ s ^ 2 ≤ Bu)

set_option maxHeartbeats 1000000 in
private lemma inv_step_lemma {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖) (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim)) (y0 : Vsp dim)
    (hy0 : y0 ∈ Xg L I) (hy0W : prj σ y0 ∉ W) :
    ∃ v ∈ Xg L I, prj σ v ∉ W ∧ ‖v‖ ≤ ‖y0‖ ∧ ∀ y ∈ Xg L I, prj σ y ∉ W → ‖v‖ ≤ ‖y‖ := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Set (Vsp dim), S = {y | y ∈ Xg L I ∧ prj σ y ∉ W ∧ ‖y‖ ≤ ‖y0‖} := ⟨_, rfl⟩
  obtain ⟨t, -, ht, hcov⟩ :=
    (isCompact_closedBall (0 : Vsp dim) ‖y0‖).finite_cover_balls (by norm_num : (0 : ℝ) < 1 / 2)
  have hex : ∀ y ∈ S, ∃ x ∈ t, y ∈ Metric.ball x (1 / 2) := by
    intro y hy
    rw [hS] at hy
    have hyb : y ∈ Metric.closedBall (0 : Vsp dim) ‖y0‖ := by
      rw [mem_closedBall_zero_iff]; exact hy.2.2
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hcov hyb)
    exact ⟨x, hx, hyx⟩
  obtain ⟨f, hf⟩ : ∃ f : Vsp dim → Vsp dim, ∀ y ∈ S, f y ∈ t ∧ y ∈ Metric.ball (f y) (1 / 2) := by
    refine ⟨fun y => if h : ∃ x ∈ t, y ∈ Metric.ball x (1 / 2) then h.choose else 0, fun y hy => ?_⟩
    have h := hex y hy
    simp only [dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn f S := by
    intro y hy y' hy' hyy
    have h1 := (hf y hy).2
    have h2 := (hf y' hy').2
    rw [hyy] at h1
    rw [Metric.mem_ball, dist_eq_norm] at h1 h2
    have hd : ‖y - y'‖ < 1 := by
      calc ‖y - y'‖ = ‖(y - f y') - (y' - f y')‖ := by congr 1; abel
        _ ≤ ‖y - f y'‖ + ‖y' - f y'‖ := norm_sub_le _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    by_contra hne
    rw [hS] at hy hy'
    have h3 := hsep (y - y') (sub_mem hy.1 hy'.1) (sub_ne_zero.mpr hne)
    linarith
  have hfin : S.Finite :=
    Set.Finite.of_finite_image (ht.subset (by rintro _ ⟨y, hy, rfl⟩; exact (hf y hy).1)) hinj
  have hne : S.Nonempty := ⟨y0, by rw [hS]; exact ⟨hy0, hy0W, le_rfl⟩⟩
  obtain ⟨v, hv, hvmin⟩ := Set.exists_min_image S (fun y => ‖y‖) hfin hne
  have hv' := hv
  rw [hS] at hv'
  refine ⟨v, hv'.1, hv'.2.1, hv'.2.2, fun y hy hyW => ?_⟩
  by_cases hle : ‖y‖ ≤ ‖y0‖
  · exact hvmin y (by rw [hS]; exact ⟨hy, hyW, hle⟩)
  · exact le_trans hv'.2.2 (le_of_lt (not_le.mp hle))

lemma inv_step [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    {L I : Submodule ℤ (Vsp dim)}
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (ρ : ℕ) (K0 Bu : ℝ) (hK0 : 0 < K0)
    (hK : (D : ℝ) * B ^ 2 / 4 ≤ K0 ^ 2)
    (hex : ∀ W : Submodule ℂ (Vsp dim), Module.finrank ℂ W < ρ →
      ∃ y ∈ Xg L I, prj σ y ∉ W ∧ ‖y‖ ^ 2 ≤ Bu)
    {k : ℕ} (hk : k < ρ) {χ w : ℕ → Vsp dim} {R μ : ℕ → ℝ} {ε : ℕ → ℕ → ℂ}
    (h : Inv L I σ ρ K0 Bu k χ w R μ ε) :
    ∃ (χ' w' : ℕ → Vsp dim) (R' μ' : ℕ → ℝ) (ε' : ℕ → ℕ → ℂ), Inv L I σ ρ K0 Bu (k + 1) χ' w' R' μ' ε' := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hwW : ∀ i < k, w i ∈ Wk σ χ k := fun i hi => Wk_mono σ χ (by omega : i + 1 ≤ k) (h2 i hi)
  obtain ⟨y0, hy0X, hy0W, hy0B⟩ := hex (Wk σ χ k) (lt_of_le_of_lt (finrank_Wk σ χ k) hk)
  obtain ⟨v, hvX, hvW, hvy0, hvmin⟩ := inv_step_lemma hsep σ (Wk σ χ k) y0 hy0X hy0W
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvW (by rw [map_zero]; exact (Wk σ χ k).zero_mem)
  have hμ1 : 1 ≤ ‖v‖ := hsep v hvX hv0
  have hρ : (1 : ℝ) ≤ ρ := by exact_mod_cast (by omega : 1 ≤ ρ)
  have hKμ : 0 < K0 * ‖v‖ := mul_pos hK0 (by linarith)
  have hTpos : 0 < (30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖ := by
    have : 0 < 30 * (ρ : ℝ) ^ 2 + 1 := by positivity
    rw [mul_assoc]; exact mul_pos this hKμ
  obtain ⟨t, χn, hto, htn, htt, hχX, hχZ, hχt, hχu⟩ := one_char hNP L I hLs hIs hiso hsep ω hω B hωB D hD σ
    (Wk σ χ k) k χ (fun j hj => h1 j hj) (fun j hj => prj_mem_Wk σ χ hj) (le_refl _)
    (fun j hj => ⟨μ j, (h9 j hj).1, fun y hy hyW => (h9 j hj).2 y hy
      (fun hm => hyW (Wk_mono σ χ (le_of_lt hj) hm))⟩)
    v hvX hvW hvmin ((30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖) hTpos
  have hK0μ : ‖χn - t‖ ≤ K0 * ‖v‖ := by
    have hsq : ‖χn - t‖ ^ 2 ≤ (K0 * ‖v‖) ^ 2 := by
      calc ‖χn - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 := hχt
        _ = (D * B ^ 2 / 4) * ‖v‖ ^ 2 := by ring
        _ ≤ K0 ^ 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hK (by positivity)
        _ = (K0 * ‖v‖) ^ 2 := by ring
    nlinarith [norm_nonneg (χn - t)]
  obtain ⟨e, he⟩ : ∃ e, e = prj σ (χn - t) := ⟨_, rfl⟩
  have heK : ‖e‖ ≤ K0 * ‖v‖ := by rw [he]; exact le_trans (norm_prj_le σ _) hK0μ
  have hpe : prj σ χn = prj σ t + e := by rw [he, map_sub]; abel
  have hproj : ∀ x : Vsp dim, ∀ j < k,
      inner ℂ (w j) (x - ∑ i ∈ Finset.range k, inner ℂ (w i) x • w i) = 0 := by
    intro x j hj
    rw [inner_sub_right, inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right, h3 j hj j hj, if_pos rfl, mul_one, sub_self]
    · intro i hi hij
      rw [inner_smul_right, h3 j hj i (Finset.mem_range.mp hi), if_neg (Ne.symm hij), mul_zero]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'
  obtain ⟨Wp, hWp⟩ : ∃ Wp, Wp = ∑ i ∈ Finset.range k, inner ℂ (w i) e • w i := ⟨_, rfl⟩
  have hWpW : Wp ∈ Wk σ χ k := by
    rw [hWp]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hwW i (Finset.mem_range.mp hi))
  have heW : ∀ j < k, inner ℂ (w j) (e - Wp) = 0 := fun j hj => by rw [hWp]; exact hproj e j hj
  have hwt : ∀ j < k, inner ℂ (w j) (prj σ t) = 0 := fun j hj => hto (w j) (hwW j hj)
  obtain ⟨q, hq⟩ : ∃ q, q = prj σ χn - Wp := ⟨_, rfl⟩
  have hqt : q = prj σ t + (e - Wp) := by rw [hq, hpe]; abel
  have hqw : ∀ j < k, inner ℂ (w j) q = 0 := fun j hj => by
    rw [hqt, inner_add_right, hwt j hj, heW j hj, add_zero]
  have hperp : inner ℂ (e - Wp) Wp = 0 := by
    nth_rewrite 2 [hWp]
    rw [inner_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [inner_smul_right, inner_eq_zero_symm.mp (heW i (Finset.mem_range.mp hi)), mul_zero]
  have heWp : ‖e - Wp‖ ≤ ‖e‖ := by
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (e - Wp) Wp hperp
    rw [sub_add_cancel] at hpy
    nlinarith [norm_nonneg (e - Wp), norm_nonneg e, norm_nonneg Wp]
  obtain ⟨Rk, hRk⟩ : ∃ Rk : ℝ, Rk = ‖q‖ := ⟨_, rfl⟩
  have hRlow : 30 * (ρ : ℝ) ^ 2 * K0 * ‖v‖ ≤ Rk := by
    have h0 : ‖prj σ t‖ ≤ ‖q‖ + ‖e - Wp‖ := by
      calc ‖prj σ t‖ = ‖q - (e - Wp)‖ := by rw [hqt]; congr 1; abel
        _ ≤ ‖q‖ + ‖e - Wp‖ := norm_sub_le _ _
    rw [htn] at h0
    rw [hRk]
    nlinarith
  have hRpos : 0 < Rk := by
    have : 0 < 30 * (ρ : ℝ) ^ 2 * K0 * ‖v‖ := by
      have h30 : 0 < 30 * (ρ : ℝ) ^ 2 := by positivity
      rw [mul_assoc]; exact mul_pos h30 hKμ
    linarith
  have hRne : (Rk : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  obtain ⟨wk, hwk⟩ : ∃ wk, wk = ((Rk : ℂ)⁻¹) • q := ⟨_, rfl⟩
  have hqR : q = (Rk : ℂ) • wk := by rw [hwk, smul_smul, mul_inv_cancel₀ hRne, one_smul]
  have hwkn : ‖wk‖ = 1 := by
    rw [hwk, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hRpos.le, ← hRk,
      inv_mul_cancel₀ hRpos.ne']
  have hwkw : ∀ j < k, inner ℂ (w j) wk = 0 := fun j hj => by
    rw [hwk, inner_smul_right, hqw j hj, mul_zero]
  obtain ⟨εk, hεk⟩ : ∃ εk : ℕ → ℂ, εk = fun i => if i < k then (starRingEnd ℂ) (inner ℂ (w i) e) / (Rk : ℂ) else 0 :=
    ⟨_, rfl⟩
  have hterm : ∀ i ∈ Finset.range k, (Rk : ℂ) • ((starRingEnd ℂ) (εk i) • w i) = inner ℂ (w i) e • w i := by
    intro i hi
    rw [hεk]
    simp only [if_pos (Finset.mem_range.mp hi)]
    rw [smul_smul, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    field_simp
  have hrep : prj σ χn = (Rk : ℂ) • (wk + ∑ i ∈ Finset.range k, (starRingEnd ℂ) (εk i) • w i) := by
    rw [smul_add, ← hqR, Finset.smul_sum, Finset.sum_congr rfl hterm, ← hWp, hq, sub_add_cancel]
  have hεsum : ∑ i ∈ Finset.range k, ‖εk i‖ ^ 2 ≤ (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2 := by
    have hON : Orthonormal ℂ (fun i : Fin k => w i) := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [h3 i i.2 j j.2]
      simp [Fin.ext_iff]
    have hB := hON.sum_inner_products_le e (s := Finset.univ)
    rw [Fin.sum_univ_eq_sum_range (fun i => ‖inner ℂ (w i) e‖ ^ 2) k] at hB
    have hs : ∑ i ∈ Finset.range k, ‖εk i‖ ^ 2 = (∑ i ∈ Finset.range k, ‖inner ℂ (w i) e‖ ^ 2) / Rk ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hεk]
      simp only [if_pos (Finset.mem_range.mp hi)]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hRpos.le, RCLike.norm_conj, div_pow]
    rw [hs]
    have hle1 : ∑ i ∈ Finset.range k, ‖inner ℂ (w i) e‖ ^ 2 ≤ (K0 * ‖v‖) ^ 2 :=
      le_trans hB (pow_le_pow_left₀ (norm_nonneg e) heK 2)
    have hRd : K0 * ‖v‖ ≤ Rk / (30 * (ρ : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc (∑ i ∈ Finset.range k, ‖inner ℂ (w i) e‖ ^ 2) / Rk ^ 2 ≤ (K0 * ‖v‖) ^ 2 / Rk ^ 2 :=
          div_le_div_of_nonneg_right hle1 (by positivity)
      _ ≤ (Rk / (30 * (ρ : ℝ) ^ 2)) ^ 2 / Rk ^ 2 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hKμ.le hRd 2) (by positivity)
      _ = (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2 := by
          have hρ0 : (ρ : ℝ) ≠ 0 := by linarith
          field_simp
  have hTt : ‖t‖ = Real.sqrt 2 * ((30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖) := by
    rw [← Real.sqrt_sq (norm_nonneg t), htt, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hTpos.le]
  have hχnorm : ‖χn‖ ≤ (Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1) * K0 * ‖v‖ := by
    calc ‖χn‖ = ‖(χn - t) + t‖ := by rw [sub_add_cancel]
      _ ≤ ‖χn - t‖ + ‖t‖ := norm_add_le _ _
      _ ≤ K0 * ‖v‖ + Real.sqrt 2 * ((30 * (ρ : ℝ) ^ 2 + 1) * K0 * ‖v‖) := by rw [hTt]; linarith
      _ = (Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1) * K0 * ‖v‖ := by ring
  have hsumw : ∀ s ≤ k, ∀ a : ℕ → ℂ, ∑ i ∈ Finset.range s, a i • Function.update w k wk i =
      ∑ i ∈ Finset.range s, a i • w i := fun s hs a =>
    Finset.sum_congr rfl fun i hi => by
      rw [Function.update_of_ne (show i ≠ k by have := Finset.mem_range.mp hi; omega)]
  refine ⟨Function.update χ k χn, Function.update w k wk, Function.update R k Rk, Function.update μ k ‖v‖,
    Function.update ε k εk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h1 s hs
    · rw [hs, Function.update_self]; exact hχX
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs), Wk_update σ χ (by omega : s + 1 ≤ k)]
      exact h2 s hs
    · rw [hs, Function.update_self, hwk]
      apply Submodule.smul_mem
      rw [hq]
      apply Submodule.sub_mem
      · have hm := prj_mem_Wk σ (Function.update χ k χn) (Nat.lt_succ_self k)
        rwa [Function.update_self] at hm
      · have h' : Wk σ (Function.update χ k χn) k = Wk σ χ k := Wk_update σ χ le_rfl χn
        apply Wk_mono σ _ (Nat.le_succ k)
        rw [h']
        exact hWpW
  · intro s hs s' hs'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs' with hs' | hs'
    · rw [Function.update_of_ne (Nat.ne_of_lt hs), Function.update_of_ne (Nat.ne_of_lt hs')]
      exact h3 s hs s' hs'
    · rw [hs', Function.update_of_ne (Nat.ne_of_lt hs), Function.update_self, hwkw s hs,
        if_neg (Nat.ne_of_lt hs)]
    · rw [hs, Function.update_self, Function.update_of_ne (Nat.ne_of_lt hs'),
        inner_eq_zero_symm.mp (hwkw s' hs'), if_neg (Nat.ne_of_lt hs').symm]
    · rw [hs, hs', Function.update_self, if_pos rfl, inner_self_eq_norm_sq_to_K, hwkn]
      norm_num
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · have hne : s ≠ k := Nat.ne_of_lt hs
      simp only [Function.update_of_ne hne]
      rw [hsumw s hs.le]
      exact h4 s hs
    · rw [hs]
      simp only [Function.update_self]
      rw [hsumw k le_rfl]
      exact hrep
  · intro s hs i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h5 s hs i hi
    · rw [hs, Function.update_self]
      simp only [hεk]
      rw [if_neg (by omega)]
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h6 s hs
    · rw [hs, Function.update_self]; exact hεsum
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · simp only [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h7 s hs
    · rw [hs]
      simp only [Function.update_self]
      exact ⟨hRlow, hχnorm⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · simp only [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h8 s hs
    · rw [hs]
      simp only [Function.update_self]
      exact ⟨hμ1, hχu⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · simp only [Function.update_of_ne (Nat.ne_of_lt hs)]
      rw [Wk_update σ χ (le_of_lt hs)]
      exact h9 s hs
    · rw [hs]
      simp only [Function.update_self]
      rw [Wk_update σ χ le_rfl]
      exact ⟨hχZ, hvmin⟩
  · intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
    · rw [Function.update_of_ne (Nat.ne_of_lt hs)]; exact h10 s hs
    · rw [hs, Function.update_self]
      exact le_trans (pow_le_pow_left₀ (norm_nonneg v) hvy0 2) hy0B

lemma inv_build [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    {L I : Submodule ℤ (Vsp dim)}
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (ρ : ℕ) (K0 Bu : ℝ) (hK0 : 0 < K0)
    (hK : (D : ℝ) * B ^ 2 / 4 ≤ K0 ^ 2)
    (hex : ∀ W : Submodule ℂ (Vsp dim), Module.finrank ℂ W < ρ →
      ∃ y ∈ Xg L I, prj σ y ∉ W ∧ ‖y‖ ^ 2 ≤ Bu) :
    ∀ k ≤ ρ, ∃ (χ w : ℕ → Vsp dim) (R μ : ℕ → ℝ) (ε : ℕ → ℕ → ℂ), Inv L I σ ρ K0 Bu k χ w R μ ε := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, ?_⟩
    unfold Inv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro s hs <;> exact absurd hs (Nat.not_lt_zero _)
  | succ k ih =>
    intro hk
    obtain ⟨χ, w, R, μ, ε, h⟩ := ih (Nat.le_of_succ_le hk)
    exact inv_step hNP hLs hIs hiso hsep ω hω B hωB D hD σ ρ K0 Bu hK0 hK hex (Nat.lt_of_succ_le hk) h

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
