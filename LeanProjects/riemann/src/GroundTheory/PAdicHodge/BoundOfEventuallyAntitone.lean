import Mathlib
import GroundTheory.PAdicHodge.ToUntiltFieldEqZeroIff
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} [CompleteSpace L]

theorem exists_adjusted {g y a b : T.RobbaExt ρ0} (hab : a * g + b * y = 1) {s : ℝ} (hs : 0 ≤ s)
    (hg1 : ∀ ρ : Set.Ioc (0 : ℝ) ρ0, s ≤ ρ → T.extNorm ρ0 ρ g = 1)
    (hgW : ∀ ρ : Set.Ioc (0 : ℝ) ρ0, s ≤ ρ → T.extNorm ρ0 ρ (g - 1) ≤ s / ρ)
    (σ : Set.Ioc (0 : ℝ) ρ0) (hσ : 2 * s ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a' b' : T.RobbaExt ρ0, a' * g + b' * y = 1 ∧ ∀ ρ : Set.Ioc (0 : ℝ) ρ0, (σ : ℝ) ≤ ρ →
      T.extNorm ρ0 ρ b' ≤ ε ∧ T.extNorm ρ0 ρ (b' * y) ≤ ε ∧
        T.extNorm ρ0 ρ (a' - 1) ≤ max ε (s / ρ) := by
  set β := max (T.extNorm ρ0 σ b) (T.extNorm ρ0 (topRad ρ0) b)
  set γ := max 1 (max (T.extNorm ρ0 σ y) (T.extNorm ρ0 (topRad ρ0) y))
  have hβ0 : 0 ≤ β := le_max_of_le_left (T.extNorm_nonneg _ _)
  have hγ1 : 1 ≤ γ := le_max_left _ _
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (β * γ + 1) by positivity)
    (show (1 : ℝ) / 2 < 1 by norm_num)
  set W := g - 1
  set t := b * ∑ j ∈ Finset.range K, (-W) ^ j
  refine ⟨a + t * y, b * (-W) ^ K, ?_, fun ρ hρ => ?_⟩
  · have hgs : g * ∑ j ∈ Finset.range K, (-W) ^ j = 1 - (-W) ^ K := by
      rw [← mul_neg_geom_sum (-W) K]
      congr 1
      simp [W]
    have : t * g = b - b * (-W) ^ K := by
      rw [show t * g = b * (g * ∑ j ∈ Finset.range K, (-W) ^ j) by simp only [t]; ring, hgs]
      ring
    linear_combination hab + y * this
  have hsρ : s ≤ ρ := by linarith [σ.2.1, hσ, hρ]
  have hρ0 := rad_pos ρ0 ρ
  have hW : T.extNorm ρ0 ρ W ≤ 1 / 2 := by
    refine (hgW ρ hsρ).trans ?_
    rw [div_le_iff₀ hρ0]
    linarith
  have hb : T.extNorm ρ0 ρ b ≤ β := T.extNorm_le_max σ (topRad ρ0) ρ hρ ρ.2.2 b
  have hy : T.extNorm ρ0 ρ y ≤ γ :=
    (T.extNorm_le_max σ (topRad ρ0) ρ hρ ρ.2.2 y).trans (le_max_right _ _)
  have hWK : T.extNorm ρ0 ρ ((-W) ^ K) ≤ (1 / 2) ^ K := by
    rw [extNorm_pow, extNorm_neg]
    exact pow_le_pow_left₀ (T.extNorm_nonneg _ _) hW K
  have hsmall : β * γ * (1 / 2) ^ K ≤ ε := by
    have h1 : (1 / 2 : ℝ) ^ K * (β * γ + 1) < ε := by
      rw [lt_div_iff₀ (by positivity)] at hK; exact hK
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) K, mul_nonneg hβ0 (zero_le_one.trans hγ1)]
  have hb' : T.extNorm ρ0 ρ (b * (-W) ^ K) ≤ β * (1 / 2) ^ K := by
    rw [extNorm_mul]
    exact mul_le_mul hb hWK (T.extNorm_nonneg _ _) hβ0
  have hby : T.extNorm ρ0 ρ (b * (-W) ^ K * y) ≤ ε := by
    rw [extNorm_mul]
    calc T.extNorm ρ0 ρ (b * (-W) ^ K) * T.extNorm ρ0 ρ y ≤ β * (1 / 2) ^ K * γ :=
          mul_le_mul hb' hy (T.extNorm_nonneg _ _) (by positivity)
      _ = β * γ * (1 / 2) ^ K := by ring
      _ ≤ ε := hsmall
  refine ⟨hb'.trans ?_, hby, ?_⟩
  · calc β * (1 / 2) ^ K ≤ β * γ * (1 / 2) ^ K := by
          have := pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) K
          nlinarith [mul_nonneg (mul_nonneg hβ0 this) (sub_nonneg.2 hγ1)]
      _ ≤ ε := hsmall
  ·
    have e : (a + t * y - 1) * g = -(b * (-W) ^ K * y + W) := by
      have hgs : g * ∑ j ∈ Finset.range K, (-W) ^ j = 1 - (-W) ^ K := by
        rw [← mul_neg_geom_sum (-W) K]
        congr 1
        simp [W]
      have : t * g = b - b * (-W) ^ K := by
        rw [show t * g = b * (g * ∑ j ∈ Finset.range K, (-W) ^ j) by simp only [t]; ring, hgs]
        ring
      linear_combination hab + y * this
    have e2 := congrArg (T.extNorm ρ0 ρ) e
    rw [extNorm_mul, hg1 ρ hsρ, mul_one, extNorm_neg] at e2
    rw [e2]
    exact (T.extNorm_add_le ρ _ _).trans (max_le_max hby (hgW ρ hsρ))

variable (hRE : T.RootExists)
include hRE

theorem exists_full_factor {x : T.RobbaExt ρ0} (hx : x ≠ 0) :
    ∃ (ls : ℕ → List T.Pt) (hl : ∀ k, ∀ P ∈ ls k, T.ptRad P.1 ≤ annHi ρ0 k) (w : T.RobbaExt ρ0),
      x = (InfProd.ofLists T ρ0 ls (annHi ρ0) annHi_nonneg tendsto_annHi hl).prod * w ∧ w ≠ 0 ∧
      (∀ k, ∀ P ∈ ls k, ∀ hr : T.ptRad P.1 ≤ ρ0, T.ptEval P.2 hr x = 0) ∧
      ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
        T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) w ≠ 0 := by
  set S0 : T.GcdSt ρ0 := ⟨x, x, hx, hx⟩
  have hl : ∀ k, ∀ P ∈ T.gcdRemoved hRE S0 k, T.ptRad P.1 ≤ annHi ρ0 k := fun k P hP =>
    ((T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.1 P hP).2
  set D := InfProd.ofLists T ρ0 (T.gcdRemoved hRE S0) (annHi ρ0) annHi_nonneg tendsto_annHi hl
  have hpart : ∀ k, D.part k = T.normProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) :=
    fun k => InfProd.ofLists_part T _ _ _ _ _ k
  have hdx : ∀ k, D.part k ∣ x := fun k => by
    rw [hpart, normProd_dvd_iff]; exact ⟨_, (T.gcdStates_spec hRE S0 k).1⟩
  obtain ⟨w, hw⟩ := D.dvd_of_forall hdx
  have hw0 : w ≠ 0 := by rintro rfl; rw [mul_zero] at hw; exact hx hw
  refine ⟨T.gcdRemoved hRE S0, hl, w, hw, hw0, ?_, ?_⟩
  · intro k P hP hr
    rw [T.ptEval_eq_zero_iff P.2 hr]
    have hmem : P ∈ (List.range (k + 1)).flatMap (T.gcdRemoved hRE S0) :=
      List.mem_flatMap.2 ⟨k, List.mem_range.2 (Nat.lt_succ_self k), hP⟩
    have hdvd : T.ξExt P.1 ρ0 ∣ T.ptProd ρ0 ((List.range (k + 1)).flatMap (T.gcdRemoved hRE S0)) :=
      List.dvd_prod (List.mem_map.2 ⟨P, hmem, rfl⟩)
    exact dvd_trans hdvd ⟨_, (T.gcdStates_spec hRE S0 (k + 1)).1⟩
  · intro Q hQ h1
    have hs0 := T.ptRad_pos' Q.2
    obtain ⟨k, hk1, hk2⟩ := exists_ann (ρ0 := ρ0) hs0 hQ
    set F := (List.range (k + 1)).flatMap (T.gcdRemoved hRE S0)
    have hQr : T.ptRad Q.1 ≤ ρ0 := hQ.trans (half_le_self ρ0.2.1.le)
    have e : T.ptProd ρ0 F * (T.gcdStates hRE S0 (k + 1)).x =
        T.ptProd ρ0 F * (T.unitProd ρ0 F * (D.shift (k + 1)).prod * w) := by
      rw [← (T.gcdStates_spec hRE S0 (k + 1)).1]
      change x = _
      rw [hw, D.prod_eq_part_mul_shift (k + 1), hpart, normProd_eq]; ring
    have hW' := mul_left_cancel₀ (T.ptProd_ne_zero F) e
    have hX : T.ptEval Q.2 hQr (T.gcdStates hRE S0 (k + 1)).x = 0 := by
      rw [hW', map_mul, h1, mul_zero]
    have hY : T.ptEval Q.2 hQr (T.gcdStates hRE S0 (k + 1)).y = 0 := by
      have : (T.gcdStates hRE S0 (k + 1)).y = (T.gcdStates hRE S0 (k + 1)).x := by
        have h1' := (T.gcdStates_spec hRE S0 (k + 1)).1
        have h2' := (T.gcdStates_spec hRE S0 (k + 1)).2
        exact (mul_left_cancel₀ (T.ptProd_ne_zero F) (h2'.symm.trans h1'))
      rw [this]; exact hX
    exact (T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.2 Q ⟨hk1, hk2⟩ ⟨hX, hY⟩

omit hRE in
theorem annHi_le_half (k : ℕ) : annHi ρ0 k ≤ (ρ0 : ℝ) / 2 := by
  unfold annHi
  exact div_le_div_of_nonneg_left ρ0.2.1.le (by norm_num)
    (by calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega))

theorem isUnit_ofRad_of_no_point {w : T.RobbaExt ρ0} (hw0 : w ≠ 0)
    (hw : ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
      T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) w ≠ 0) :
    IsUnit (T.ofRad ρ0 w) := by
  set ρ1 := halfRad ρ0
  have hρ1 : (ρ1 : ℝ) = (ρ0 : ℝ) / 2 := rfl
  have hw1 : T.res (halfRad_le ρ0) w ≠ 0 := fun h0 => hw0 (T.res_injective _ (h0.trans (map_zero _).symm))
  rw [← T.ofRad_res (halfRad_le ρ0)]
  refine T.isUnit_ofRad_of_mult_eq_zero hw1 fun σ hσ0 hσ1 => ?_
  rw [T.mult_res (halfRad_le ρ0) w ⟨hσ0, hσ1⟩]
  by_contra hm
  have hm1 : 1 ≤ T.mult w σ := by have := T.mult_nonneg w σ; omega
  have hσρ0 : σ < ρ0 := hσ1.trans_le (halfRad_le ρ0)
  obtain ⟨ξ, hξ, hr, y, hy⟩ := hRE ρ0 w hw0 σ hσ0 hσρ0 hm1
  have hQ : T.ptRad ξ ≤ (ρ0 : ℝ) / 2 := by rw [hr, ← hρ1]; exact hσ1.le
  exact hw ⟨ξ, hξ⟩ hQ ((T.ptEval_eq_zero_iff hξ _ w).2 ⟨y, hy⟩)

omit hRE in
theorem bound_of_eventually_antitone {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) {k1 : ℕ}
    (h : ∀ k ≥ k1, c (k + 1) ≤ c k) : ∃ M, ∀ k, c k ≤ M := by
  refine ⟨∑ j ∈ Finset.range (k1 + 1), c j, fun k => ?_⟩
  have hsum : ∀ j ≤ k1, c j ≤ ∑ j ∈ Finset.range (k1 + 1), c j := fun j hj =>
    Finset.single_le_sum (fun i _ => hc0 i) (Finset.mem_range.2 (by omega))
  rcases le_total k k1 with hk | hk
  · exact hsum k hk
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction i with
    | zero => exact hsum k1 le_rfl
    | succ i ih => exact (h (k1 + i) (by omega)).trans (ih (by omega))

theorem one_mem_span_of_coprime {x y : T.RobbaExt ρ0} (hx : x ≠ 0)
    (hcop : ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
      ¬ (T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) x = 0 ∧
        T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) y = 0)) :
    (1 : T.RobbaTilde) ∈ Ideal.span {T.ofRad ρ0 x, T.ofRad ρ0 y} := by
  obtain ⟨ls, hl, w, hxw, hw0, hlx, hwnz⟩ := T.exists_full_factor hRE hx
  set D := InfProd.ofLists T ρ0 ls (annHi ρ0) annHi_nonneg tendsto_annHi hl
  have hDg : ∀ k, D.g k = T.normProd ρ0 (ls k) := fun k => rfl

  have hAB : ∀ k, ∃ a b : T.RobbaExt ρ0, a * D.g k + b * y = 1 := by
    intro k
    rw [hDg]
    refine T.exists_bezout_list y (ls k) fun P hP => ⟨(hl k P hP).trans
      ((annHi_le_half k).trans (half_le_self ρ0.2.1.le)), fun h0 => ?_⟩
    have hQ : T.ptRad P.1 ≤ (ρ0 : ℝ) / 2 := (hl k P hP).trans (annHi_le_half k)
    exact hcop P hQ ⟨hlx k P hP _, h0⟩
  have hσ : ∀ k : ℕ, 0 < 2 * annHi ρ0 k ∧ 2 * annHi ρ0 k ≤ ρ0 := fun k => by
    refine ⟨by have := annLo_pos (ρ0 := ρ0) k; have := annLo_le (ρ0 := ρ0) k; linarith, ?_⟩
    have := annHi_le_half (ρ0 := ρ0) k; linarith
  have hAdj : ∀ k, ∃ a' b' : T.RobbaExt ρ0, a' * D.g k + b' * y = 1 ∧
      ∀ ρ : Set.Ioc (0 : ℝ) ρ0, 2 * annHi ρ0 k ≤ ρ →
        T.extNorm ρ0 ρ b' ≤ (1 / 2) ^ k ∧ T.extNorm ρ0 ρ (b' * y) ≤ (1 / 2) ^ k ∧
          T.extNorm ρ0 ρ (a' - 1) ≤ max ((1 / 2) ^ k) (annHi ρ0 k / ρ) := by
    intro k
    obtain ⟨a, b, hab⟩ := hAB k
    rw [hDg] at hab ⊢
    exact T.exists_adjusted hab (annHi_nonneg k)
      (fun ρ hρ => (T.norm_normProd_of_le (annHi_nonneg k) (hl k) ρ hρ).1)
      (fun ρ hρ => (T.norm_normProd_of_le (annHi_nonneg k) (hl k) ρ hρ).2)
      ⟨2 * annHi ρ0 k, (hσ k).1, (hσ k).2⟩ le_rfl (by positivity)
  choose a' b' hab' hbnd using hAdj
  set A : ℕ → T.RobbaExt ρ0 := fun k => ∏ j ∈ Finset.range k, a' j
  set B : ℕ → T.RobbaExt ρ0 := fun k => ∑ j ∈ Finset.range k, A j * D.part j * b' j
  have hA : ∀ k, A (k + 1) = A k * a' k := fun k => Finset.prod_range_succ _ _
  have hB : ∀ k, B (k + 1) = B k + A k * D.part k * b' k := fun k => Finset.sum_range_succ _ _
  have hinv : ∀ k, A k * D.part k + B k * y = 1 := by
    intro k
    induction k with
    | zero => simp [A, B, InfProd.part_zero]
    | succ k ih =>
      rw [hA, hB, InfProd.part_succ]
      linear_combination ih + A k * D.part k * hab' k

  have hconv : ∀ ρ : Set.Ioc (0 : ℝ) ρ0,
      Tendsto (fun k => T.extNorm ρ0 ρ (A (k + 1) - A k)) atTop (𝓝 0) ∧
        Tendsto (fun k => T.extNorm ρ0 ρ (B (k + 1) - B k)) atTop (𝓝 0) := by
    intro ρ
    have hρ := rad_pos ρ0 ρ
    have hs : Tendsto (fun k => 2 * annHi ρ0 k) atTop (𝓝 0) := by
      simpa using (tendsto_annHi (ρ0 := ρ0)).const_mul 2
    have he : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hsr : Tendsto (fun k => annHi ρ0 k / ρ) atTop (𝓝 0) := by
      simpa using (tendsto_annHi (ρ0 := ρ0)).div_const (ρ : ℝ)
    have hm : Tendsto (fun k => max ((1 / 2 : ℝ) ^ k) (annHi ρ0 k / ρ)) atTop (𝓝 0) := by
      simpa using he.max hsr
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hs.eventually (ge_mem_nhds hρ))
    obtain ⟨k1, hk1⟩ := eventually_atTop.1 (hm.eventually (gt_mem_nhds one_pos))
    have ha1 : ∀ k ≥ max k0 k1, T.extNorm ρ0 ρ (a' k) ≤ 1 := by
      intro k hk
      have h1 := (hbnd k ρ (hk0 k (le_of_max_le_left hk))).2.2
      have h2 := hk1 k (le_of_max_le_right hk)
      have := T.extNorm_add_le ρ (a' k - 1) 1
      rw [sub_add_cancel, extNorm_one] at this
      exact this.trans (max_le (h1.trans h2.le) le_rfl)
    obtain ⟨M, hM⟩ := bound_of_eventually_antitone (c := fun k => T.extNorm ρ0 ρ (A k))
      (fun k => T.extNorm_nonneg _ _) (k1 := max k0 k1) fun k hk => by
        rw [hA, extNorm_mul]
        exact mul_le_of_le_one_right (T.extNorm_nonneg _ _) (ha1 k hk)
    obtain ⟨CP, hCP⟩ := D.exists_bound ρ
    have hM0 : 0 ≤ M := (T.extNorm_nonneg _ _).trans (hM 0)
    have hCP0 : 0 ≤ CP := (T.extNorm_nonneg _ _).trans (hCP 0)
    refine ⟨?_, ?_⟩
    · have hlim := hm.const_mul M
      rw [mul_zero] at hlim
      refine squeeze_zero' (Eventually.of_forall fun k => T.extNorm_nonneg _ _) ?_ hlim
      filter_upwards [eventually_ge_atTop k0] with k hk
      rw [hA, show A k * a' k - A k = A k * (a' k - 1) by ring, extNorm_mul]
      exact mul_le_mul (hM k) (hbnd k ρ (hk0 k hk)).2.2 (T.extNorm_nonneg _ _) hM0
    · have hlim := he.const_mul (M * CP)
      rw [mul_zero] at hlim
      refine squeeze_zero' (Eventually.of_forall fun k => T.extNorm_nonneg _ _) ?_ hlim
      filter_upwards [eventually_ge_atTop k0] with k hk
      rw [hB, add_sub_cancel_left, extNorm_mul, extNorm_mul]
      exact mul_le_mul (mul_le_mul (hM k) (hCP k) (T.extNorm_nonneg _ _) hM0)
        (hbnd k ρ (hk0 k hk)).1 (T.extNorm_nonneg _ _) (mul_nonneg hM0 hCP0)
  obtain ⟨Al, hAl⟩ := cauchySeq_tendsto_of_complete (T.cauchySeq_of_increments fun ρ => (hconv ρ).1)
  obtain ⟨Bl, hBl⟩ := cauchySeq_tendsto_of_complete (T.cauchySeq_of_increments fun ρ => (hconv ρ).2)
  have hlim : Tendsto (fun k => A k * D.part k + B k * y) atTop (𝓝 (Al * D.prod + Bl * y)) :=
    (hAl.mul D.tendsto_part).add (hBl.mul tendsto_const_nhds)
  have hconst : (fun k => A k * D.part k + B k * y) = fun _ => (1 : T.RobbaExt ρ0) := funext hinv
  rw [hconst] at hlim
  have hrel : Al * D.prod + Bl * y = 1 := (tendsto_nhds_unique tendsto_const_nhds hlim).symm

  obtain ⟨u, hu⟩ := (T.isUnit_ofRad_of_no_point hRE hw0 hwnz).exists_right_inv
  rw [Ideal.mem_span_pair]
  refine ⟨T.ofRad ρ0 Al * u, T.ofRad ρ0 Bl, ?_⟩
  have e := congrArg (T.ofRad ρ0) hrel
  rw [map_add, map_mul, map_mul, map_one] at e
  rw [hxw, map_mul, ← e]
  linear_combination T.ofRad ρ0 Al * T.ofRad ρ0 D.prod * hu

theorem isBezout_of_rootExists : IsBezout T.RobbaTilde := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  by_cases hx : x = 0
  · subst hx
    refine ⟨⟨y, ?_⟩⟩
    rw [Ideal.span_insert_zero]
  by_cases hy : y = 0
  · subst hy
    refine ⟨⟨x, ?_⟩⟩
    rw [Set.pair_comm, Ideal.span_insert_zero]
  obtain ⟨ρ0, x0, y0, rfl, rfl⟩ := T.exists_ofRad₂ x y
  have hx0 : x0 ≠ 0 := by rintro rfl; exact hx (map_zero _)
  have hy0 : y0 ≠ 0 := by rintro rfl; exact hy (map_zero _)
  obtain ⟨d, x', y', hd, hx', hy', hcop⟩ := T.exists_gcd hRE hx0 hy0
  have hx'0 : x' ≠ 0 := by rintro rfl; rw [mul_zero] at hx'; exact hx0 hx'
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (T.one_mem_span_of_coprime hRE hx'0 hcop)
  refine ⟨⟨T.ofRad ρ0 d, le_antisymm ?_ ?_⟩⟩
  · rw [Ideal.span_le]
    rintro z hz
    rcases hz with rfl | rfl
    · rw [hx', map_mul]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · rw [hy', map_mul]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have e : T.ofRad ρ0 d = a * T.ofRad ρ0 x0 + b * T.ofRad ρ0 y0 := by
      rw [hx', hy', map_mul, map_mul]
      linear_combination (-(T.ofRad ρ0 d)) * hab
    rw [SetLike.mem_coe, e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

end TeichLift

end GroundTheory.PAdicHodge
