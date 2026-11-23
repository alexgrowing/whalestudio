import Mathlib
import GroundTheory.PAdicHodge.RobbaAmice
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

theorem gaussNorm_single' (k : ℤ) (c : K) {ρ : ℝ} (hρ : 0 < ρ) :
    gaussNorm (Pi.single k c) ρ = ‖c‖ * ρ ^ k := by
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · by_cases hn : n = k
    · subst hn; simp
    · simp [hn]; positivity
  · simpa using (convergesAt_single k c ρ).le_gaussNorm k

theorem gaussNorm_cmul' {a b : ℤ → K} {ρ : ℝ} (hρ : 0 < ρ) (ha : ConvergesAt a ρ)
    (hb : ConvergesAt b ρ) : gaussNorm (cmul a b) ρ = gaussNorm a ρ * gaussNorm b ρ := by
  by_cases ha0 : a = 0
  · subst ha0; simp [zero_cmul, gaussNorm_zero]
  by_cases hb0 : b = 0
  · subst hb0; simp [cmul_zero, gaussNorm_zero]
  exact gaussNorm_cmul hρ ha hb ha0 hb0

theorem tendsto_zpow_atTop_of_lt_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    Tendsto (fun n : ℤ => t ^ n) atTop (𝓝 0) := by
  have ht : Tendsto Int.toNat atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by omega⟩
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp ht
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
  simp [Function.comp, ← zpow_natCast, Int.toNat_of_nonneg hn]

theorem convergesAt_of_bounded {a : ℤ → K} {ρ₁ ρ ρ₂ C₁ C₂ : ℝ} (h₁ : 0 < ρ₁) (h1 : ρ₁ < ρ)
    (h2 : ρ < ρ₂) (hC₁ : ∀ n, ‖a n‖ * ρ₁ ^ n ≤ C₁) (hC₂ : ∀ n, ‖a n‖ * ρ₂ ^ n ≤ C₂) :
    ConvergesAt a ρ := by
  have hρ : 0 < ρ := h₁.trans h1
  have hρ₂ : 0 < ρ₂ := hρ.trans h2
  unfold ConvergesAt
  rw [Int.cofinite_eq]
  refine tendsto_sup.2 ⟨?_, ?_⟩
  ·
    have ht : Tendsto (fun n : ℤ => (ρ₁ / ρ) ^ (-n)) atBot (𝓝 0) :=
      (tendsto_zpow_atTop_of_lt_one (by positivity) ((div_lt_one hρ).2 h1)).comp tendsto_neg_atBot_atTop
    have := ht.const_mul C₁
    rw [mul_zero] at this
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) this
    have e : ρ ^ n = ρ₁ ^ n * (ρ₁ / ρ) ^ (-n) := by
      rw [div_zpow, zpow_neg, zpow_neg, inv_div_inv, mul_div_cancel₀ _ (zpow_ne_zero _ h₁.ne')]
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC₁ n) (by positivity)
  · have ht := tendsto_zpow_atTop_of_lt_one (t := ρ / ρ₂) (by positivity) ((div_lt_one hρ₂).2 h2)
    have := ht.const_mul C₂
    rw [mul_zero] at this
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) this
    have e : ρ ^ n = ρ₂ ^ n * (ρ / ρ₂) ^ n := by
      rw [div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ hρ₂.ne')]
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC₂ n) (by positivity)

end Laurent

namespace Robba

variable {f g : Robba K} {ρ : ℝ}

theorem gaussNorm_mul (hρ : 0 < ρ) (hf : ConvergesAt f.coeff ρ) (hg : ConvergesAt g.coeff ρ) :
    gaussNorm (f * g).coeff ρ = gaussNorm f.coeff ρ * gaussNorm g.coeff ρ :=
  gaussNorm_cmul' hρ hf hg

theorem convergesAt_mul (hρ : 0 < ρ) (hf : ConvergesAt f.coeff ρ) (hg : ConvergesAt g.coeff ρ) :
    ConvergesAt (f * g).coeff ρ := hf.cmul hρ hg

theorem gaussNorm_single (k : ℤ) (c : K) (hρ : 0 < ρ) :
    gaussNorm (single k c).coeff ρ = ‖c‖ * ρ ^ k := gaussNorm_single' k c hρ

theorem convergesAt_single' (k : ℤ) (c : K) (ρ : ℝ) : ConvergesAt (single k c).coeff ρ :=
  convergesAt_single k c ρ

theorem convergesAt_add (hρ : 0 < ρ) (hf : ConvergesAt f.coeff ρ) (hg : ConvergesAt g.coeff ρ) :
    ConvergesAt (f + g).coeff ρ := hf.add hρ hg

theorem convergesAt_sub (hρ : 0 < ρ) (hf : ConvergesAt f.coeff ρ) (hg : ConvergesAt g.coeff ρ) :
    ConvergesAt (f - g).coeff ρ := hf.sub hρ hg

theorem convergesAt_neg (hf : ConvergesAt f.coeff ρ) : ConvergesAt (-f).coeff ρ := hf.neg

theorem gaussNorm_add_le' (hρ : 0 < ρ) (hf : ConvergesAt f.coeff ρ) (hg : ConvergesAt g.coeff ρ) :
    gaussNorm (f + g).coeff ρ ≤ max (gaussNorm f.coeff ρ) (gaussNorm g.coeff ρ) :=
  gaussNorm_add_le hρ hf hg

theorem gaussNorm_neg' (f : Robba K) (ρ : ℝ) : gaussNorm (-f).coeff ρ = gaussNorm f.coeff ρ :=
  gaussNorm_neg _ _

theorem single_pow (k : ℤ) (n : ℕ) : (single k (1 : K)) ^ n = single (k * n) 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, single_mul_single]; congr 1 <;> push_cast <;> ring

theorem exists_Ico_of_eventually {P : ℝ → Prop} (h : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), P ρ) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ ρ, r ≤ ρ → ρ < 1 → P ρ := by
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h
  refine ⟨(max l (1 / 2) + 1) / 2, by positivity, ?_, fun ρ h1 h2 => hsub ⟨?_, h2⟩⟩
  · have : max l (1 / 2) < 1 := max_lt hl (by norm_num)
    linarith
  · have := le_max_left l (1 / 2)
    have : max l (1 / 2) < 1 := max_lt hl (by norm_num)
    linarith

theorem eventually_convergesAt (f : Robba K) : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ConvergesAt f.coeff ρ := by
  obtain ⟨r, hr0, hr1, h⟩ := exists_common f f
  filter_upwards [Ioo_mem_nhdsLT hr1] with ρ hρ
  exact (h ρ hρ.1.le hρ.2).1

end Robba

variable (K) in

structure FrobeniusLift where

  q : ℕ
  one_lt_q : 1 < q

  σ : K →+* K
  norm_σ : ∀ x, ‖σ x‖ = ‖x‖
  norm_σ_sub_pow_lt : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ q‖ < 1

  u : Robba K
  u_mem : u ∈ Robba.bounded K
  gaussNorm_u_sub_single_lt_one : Robba.norm1 (u - Robba.single q 1) < 1

namespace FrobeniusLift

variable (F : FrobeniusLift K)

def c : Robba K := F.u - Robba.single F.q 1

theorem c_mem : F.c ∈ Robba.bounded K :=
  (Robba.bounded K).sub_mem F.u_mem (Robba.single_mem_bounded _ _)

theorem q_pos : 0 < F.q := lt_trans zero_lt_one F.one_lt_q

theorem eventually_gaussNorm_c_lt :
    ∀ᶠ ρ in 𝓝[<] (1 : ℝ), gaussNorm F.c.coeff ρ < ρ ^ F.q := by
  have h1 := Robba.tendsto_gaussNorm_norm1 F.c_mem
  have h2 : Tendsto (fun ρ : ℝ => ρ ^ F.q) (𝓝[<] 1) (𝓝 1) := by
    have := ((continuous_pow F.q).tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  exact h1.eventually_lt h2 F.gaussNorm_u_sub_single_lt_one

theorem isUnit_u : IsUnit F.u := by
  obtain ⟨r, hr0, hr1, hr⟩ := Robba.exists_Ico_of_eventually
    (F.eventually_gaussNorm_c_lt.and F.c.eventually_convergesAt)
  have hT : IsUnit (Robba.single (F.q : ℤ) (1 : K)) := Robba.isUnit_single _ one_ne_zero
  have key : F.u = Robba.single (F.q : ℤ) 1 * (1 + Robba.single (-(F.q : ℤ)) 1 * F.c) := by
    rw [mul_add, mul_one, ← mul_assoc, Robba.single_mul_single, add_neg_cancel, mul_one,
      Robba.single_zero_one, one_mul, c, add_sub_cancel]
  rw [key]
  refine hT.mul (Robba.isUnit_one_add hr0 hr1 fun ρ h1 h2 => ?_)
  have hρ : 0 < ρ := hr0.trans_le h1
  obtain ⟨hlt, hconv⟩ := hr ρ h1 h2
  refine ⟨Robba.convergesAt_mul hρ (Robba.convergesAt_single' _ _ _) hconv, ?_⟩
  rw [Robba.gaussNorm_mul hρ (Robba.convergesAt_single' _ _ _) hconv, Robba.gaussNorm_single _ _ hρ,
    norm_one, one_mul, zpow_neg, zpow_natCast, inv_mul_lt_iff₀ (by positivity), mul_one]
  exact hlt

def uu : (Robba K)ˣ := F.isUnit_u.unit

@[simp] theorem coe_uu : (F.uu : Robba K) = F.u := rfl

theorem exists_radius : ∃ r₀, 0 < r₀ ∧ r₀ < 1 ∧ ∀ ρ, r₀ ≤ ρ → ρ < 1 →
    ConvergesAt F.u.coeff ρ ∧ ConvergesAt ((F.uu⁻¹ : (Robba K)ˣ) : Robba K).coeff ρ ∧
    gaussNorm F.c.coeff ρ < ρ ^ F.q :=
  Robba.exists_Ico_of_eventually (F.u.eventually_convergesAt.and
    ((((F.uu⁻¹ : (Robba K)ˣ) : Robba K).eventually_convergesAt).and F.eventually_gaussNorm_c_lt))

def r₀ : ℝ := F.exists_radius.choose

theorem r₀_pos : 0 < F.r₀ := F.exists_radius.choose_spec.1
theorem r₀_lt_one : F.r₀ < 1 := F.exists_radius.choose_spec.2.1
theorem r₀_spec {ρ : ℝ} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) :
    ConvergesAt F.u.coeff ρ ∧ ConvergesAt ((F.uu⁻¹ : (Robba K)ˣ) : Robba K).coeff ρ ∧
    gaussNorm F.c.coeff ρ < ρ ^ F.q :=
  F.exists_radius.choose_spec.2.2 ρ h1 h2

def U (n : ℤ) : ℤ → K := ((F.uu ^ n : (Robba K)ˣ) : Robba K).coeff

theorem U_add (i k : ℤ) : F.U (i + k) = cmul (F.U i) (F.U k) := by
  simp only [U, zpow_add, Units.val_mul, Robba.coeff_mul]

theorem U_zero : F.U 0 = Pi.single 0 1 := by simp [U]

theorem U_one : F.U 1 = F.u.coeff := by simp [U]

def δ (ρ : ℝ) : ℝ := gaussNorm F.c.coeff ρ / ρ ^ F.q

variable {F}

theorem δ_lt_one {ρ : ℝ} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) : F.δ ρ < 1 := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  rw [δ, div_lt_one (by positivity)]
  exact (F.r₀_spec h1 h2).2.2

theorem δ_nonneg {ρ : ℝ} (hρ : 0 < ρ) : 0 ≤ F.δ ρ := by
  unfold δ; have := gaussNorm_nonneg (a := F.c.coeff) hρ; positivity

theorem convergesAt_c {ρ : ℝ} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) : ConvergesAt F.c.coeff ρ := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  exact (F.r₀_spec h1 h2).1.sub hρ (convergesAt_single _ _ _)

theorem gaussNorm_c {ρ : ℝ} (hρ : 0 < ρ) : gaussNorm F.c.coeff ρ = F.δ ρ * ρ ^ F.q := by
  rw [δ, div_mul_cancel₀ _ (by positivity)]

theorem U_spec {ρ : ℝ} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) (n : ℤ) :
    ConvergesAt (F.U n) ρ ∧
      gaussNorm (F.U n - Pi.single ((F.q : ℤ) * n) 1) ρ ≤ F.δ ρ * (ρ ^ F.q) ^ n := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  obtain ⟨hu, hv, -⟩ := F.r₀_spec h1 h2
  have hc := convergesAt_c h1 h2
  have hδ0 := δ_nonneg (F := F) hρ
  have hδ1 := δ_lt_one h1 h2
  set v := ((F.uu⁻¹ : (Robba K)ˣ) : Robba K)
  set T := Robba.single (F.q : ℤ) (1 : K)
  set Ti := Robba.single (-(F.q : ℤ)) (1 : K)
  have hTc : ConvergesAt T.coeff ρ := Robba.convergesAt_single' _ _ _
  have hTic : ConvergesAt Ti.coeff ρ := Robba.convergesAt_single' _ _ _
  have hTn : gaussNorm T.coeff ρ = ρ ^ F.q := by
    rw [Robba.gaussNorm_single _ _ hρ, norm_one, one_mul, zpow_natCast]
  have hTin : gaussNorm Ti.coeff ρ = (ρ ^ F.q)⁻¹ := by
    rw [Robba.gaussNorm_single _ _ hρ, norm_one, one_mul, zpow_neg, zpow_natCast]
  have huT : F.u = T + F.c := by rw [c]; abel
  have hqpos : 0 < ρ ^ F.q := by positivity

  have hun : gaussNorm F.u.coeff ρ ≤ ρ ^ F.q := by
    have := Robba.gaussNorm_add_le' hρ hTc hc
    rw [← huT, hTn, gaussNorm_c hρ] at this
    refine this.trans (max_le le_rfl ?_)
    nlinarith

  have hvid : v - Ti = -(Ti * F.c * v) := by
    have huv : F.u * v = 1 := by simp [v]
    have hTT : Ti * T = 1 := by
      simp only [Ti, T, Robba.single_mul_single, neg_add_cancel, mul_one, Robba.single_zero_one]
    have : Ti * F.c * v = Ti * (F.u * v) - (Ti * T) * v := by rw [c]; ring
    rw [this, huv, hTT]; ring
  have hcv : ConvergesAt (Ti * F.c * v).coeff ρ :=
    Robba.convergesAt_mul hρ (Robba.convergesAt_mul hρ hTic hc) hv
  have hTcv : gaussNorm (Ti * F.c * v).coeff ρ = F.δ ρ * gaussNorm v.coeff ρ := by
    rw [Robba.gaussNorm_mul hρ (Robba.convergesAt_mul hρ hTic hc) hv, Robba.gaussNorm_mul hρ hTic hc,
      hTin, gaussNorm_c hρ]
    field_simp

  have hvn : gaussNorm v.coeff ρ ≤ (ρ ^ F.q)⁻¹ := by
    have e : v = Ti + (v - Ti) := by abel
    have := Robba.gaussNorm_add_le' hρ hTic (Robba.convergesAt_sub hρ hv hTic)
    rw [← e, hvid, Robba.gaussNorm_neg', hTcv, hTin] at this
    by_contra hcon
    rw [not_le] at hcon
    have hpos : 0 < gaussNorm v.coeff ρ := lt_trans (by positivity) hcon
    rcases le_max_iff.1 this with h | h
    · linarith
    · nlinarith
  have hvTn : gaussNorm (v - Ti).coeff ρ ≤ F.δ ρ * (ρ ^ F.q)⁻¹ := by
    rw [hvid, Robba.gaussNorm_neg', hTcv]
    exact mul_le_mul_of_nonneg_left hvn hδ0
  have hcn : gaussNorm F.c.coeff ρ ≤ F.δ ρ * ρ ^ F.q := (gaussNorm_c hρ).le

  let e : ℤ → Robba K := fun n => Robba.single ((F.q : ℤ) * n) 1
  have hec : ∀ n, ConvergesAt (e n).coeff ρ := fun n => Robba.convergesAt_single' _ _ _
  have hen : ∀ n : ℤ, gaussNorm (e n).coeff ρ = (ρ ^ F.q) ^ n := fun n => by
    rw [Robba.gaussNorm_single _ _ hρ, norm_one, one_mul, zpow_mul, zpow_natCast]
  let w : ℤ → Robba K := fun n => ((F.uu ^ n : (Robba K)ˣ) : Robba K)

  have step : ∀ (x y ex ey : Robba K) (A B : ℝ), 0 ≤ A → 0 ≤ B →
      ConvergesAt x.coeff ρ → ConvergesAt y.coeff ρ → ConvergesAt ex.coeff ρ →
      ConvergesAt ey.coeff ρ → gaussNorm ex.coeff ρ = A → gaussNorm ey.coeff ρ = B →
      gaussNorm (x - ex).coeff ρ ≤ F.δ ρ * A → gaussNorm (y - ey).coeff ρ ≤ F.δ ρ * B →
      gaussNorm y.coeff ρ ≤ B →
      gaussNorm (x * y - ex * ey).coeff ρ ≤ F.δ ρ * (A * B) := by
    intro x y ex ey A B hA hB hx hy hex hey hexn heyn hxe hye hyn
    have id : x * y - ex * ey = (x - ex) * y + ex * (y - ey) := by ring
    have s1 := Robba.convergesAt_sub hρ hx hex
    have s2 := Robba.convergesAt_sub hρ hy hey
    have c1 := Robba.convergesAt_mul hρ s1 hy
    have c2 := Robba.convergesAt_mul hρ hex s2
    have := Robba.gaussNorm_add_le' hρ c1 c2
    rw [← id, Robba.gaussNorm_mul hρ s1 hy, Robba.gaussNorm_mul hρ hex s2, hexn] at this
    refine this.trans (max_le ?_ ?_)
    · calc gaussNorm (x - ex).coeff ρ * gaussNorm y.coeff ρ ≤ (F.δ ρ * A) * B :=
            mul_le_mul hxe hyn (gaussNorm_nonneg hρ) (by positivity)
        _ = _ := by ring
    · calc A * gaussNorm (y - ey).coeff ρ ≤ A * (F.δ ρ * B) := mul_le_mul_of_nonneg_left hye hA
        _ = _ := by ring
  have P : ∀ n : ℤ, ConvergesAt (w n).coeff ρ ∧
      gaussNorm (w n - e n).coeff ρ ≤ F.δ ρ * (ρ ^ F.q) ^ n := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      refine ⟨by simpa [w] using convergesAt_single 0 (1 : K) ρ, ?_⟩
      have : w 0 - e 0 = 0 := by simp [w, e]
      rw [this, Robba.coeff_zero, gaussNorm_zero]; positivity
    | succ i ih =>
      have hw : w (i + 1) = w i * F.u := by simp [w, zpow_add_one]
      have he : e (i + 1) = e i * T := by
        simp only [e, T, Robba.single_mul_single, mul_one]; congr 1; try ring
      refine ⟨by rw [hw]; exact Robba.convergesAt_mul hρ ih.1 hu, ?_⟩
      rw [hw, he, zpow_add_one₀ hqpos.ne']
      exact step _ _ _ _ _ _ (by positivity) hqpos.le ih.1 hu (hec i) hTc (hen i) hTn ih.2
        (by rw [huT, add_sub_cancel_left]; exact hcn) hun
    | pred i ih =>
      have hw : w (-(i : ℤ) - 1) = w (-(i : ℤ)) * v := by
        simp [w, v, zpow_sub_one]
      have he : e (-(i : ℤ) - 1) = e (-(i : ℤ)) * Ti := by
        simp only [e, Ti, Robba.single_mul_single, mul_one]; congr 1; try ring
      refine ⟨by rw [hw]; exact Robba.convergesAt_mul hρ ih.1 hv, ?_⟩
      rw [hw, he, zpow_sub_one₀ hqpos.ne']
      exact step _ _ _ _ _ _ (by positivity) (by positivity) ih.1 hv (hec _) hTic (hen _) hTin
        ih.2 hvTn hvn
  refine ⟨(P n).1, ?_⟩
  have := (P n).2
  simpa [w, e, U] using this

theorem convergesAt_U {ρ : ℝ} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) (n : ℤ) : ConvergesAt (F.U n) ρ :=
  (U_spec h1 h2 n).1

theorem gaussNorm_U_le {ρ : ℝ} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) (n : ℤ) :
    gaussNorm (F.U n) ρ ≤ (ρ ^ F.q) ^ n := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have hs : ConvergesAt (Pi.single ((F.q : ℤ) * n) (1 : K)) ρ := convergesAt_single _ _ _
  have e : F.U n = Pi.single ((F.q : ℤ) * n) 1 + (F.U n - Pi.single ((F.q : ℤ) * n) 1) := by abel
  have := gaussNorm_add_le hρ hs ((convergesAt_U h1 h2 n).sub hρ hs)
  rw [← e, gaussNorm_single' _ _ hρ, norm_one, one_mul, zpow_mul, zpow_natCast] at this
  refine this.trans (max_le le_rfl ((U_spec h1 h2 n).2.trans ?_))
  have := δ_lt_one h1 h2
  have : 0 < (ρ ^ F.q) ^ n := by positivity
  nlinarith [δ_nonneg (F := F) hρ]

theorem norm_U_le {ρ : ℝ} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) (n m : ℤ) :
    ‖F.U n m‖ * ρ ^ m ≤ (ρ ^ F.q) ^ n :=
  ((convergesAt_U h1 h2 n).le_gaussNorm m).trans (gaussNorm_U_le h1 h2 n)

end FrobeniusLift

namespace FrobeniusLift

variable {F : FrobeniusLift K}

theorem tendsto_pow_q : Tendsto (fun ρ : ℝ => ρ ^ F.q) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((continuous_pow F.q).tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact pow_lt_one₀ hρ.1.le hρ.2 F.q_pos.ne'

theorem eventually_r₀_le : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), F.r₀ ≤ ρ := by
  filter_upwards [Ioo_mem_nhdsLT F.r₀_lt_one] with ρ hρ using hρ.1.le

theorem eventually_convergesAt_pow (f : Robba K) :
    ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ConvergesAt f.coeff (ρ ^ F.q) :=
  tendsto_pow_q.eventually f.eventually_convergesAt

variable (F) in

def phiSeq (f : ℤ → K) (m : ℤ) : K := ∑' n, F.σ (f n) * F.U n m

variable {ρ : ℝ}

theorem norm_phi_term_le (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) (f : ℤ → K) (n m : ℤ) :
    ‖F.σ (f n) * F.U n m‖ * ρ ^ m ≤ ‖f n‖ * (ρ ^ F.q) ^ n := by
  rw [norm_mul, F.norm_σ, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_U_le h1 h2 n m) (norm_nonneg _)

theorem tendsto_phi_term (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (m : ℤ) :
    Tendsto (fun n => F.σ (f n) * F.U n m) cofinite (𝓝 0) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have hρm : 0 < ρ ^ m := zpow_pos hρ m
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := hf.div_const (ρ ^ m)
  rw [zero_div] at this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) this
  rw [le_div_iff₀ hρm]
  exact norm_phi_term_le h1 h2 f n m

theorem summable_phi_term (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (m : ℤ) : Summable (fun n => F.σ (f n) * F.U n m) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_phi_term h1 h2 hf m)

theorem phiSeq_weight_le (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (m : ℤ) :
    ‖F.phiSeq f m‖ * ρ ^ m ≤ gaussNorm f (ρ ^ F.q) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have hρm : 0 < ρ ^ m := zpow_pos hρ m
  rw [← le_div_iff₀ hρm]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (div_nonneg (gaussNorm_nonneg (by positivity)) hρm.le) fun n => ?_
  rw [le_div_iff₀ hρm]
  exact (norm_phi_term_le h1 h2 f n m).trans (hf.le_gaussNorm n)

theorem phiSeq_convergesAt {ρ₁ ρ₂ : ℝ} (h1 : F.r₀ ≤ ρ₁) (h12 : ρ₁ < ρ) (h2 : ρ < ρ₂)
    (h2' : ρ₂ < 1) {f : ℤ → K} (hf1 : ConvergesAt f (ρ₁ ^ F.q))
    (hf2 : ConvergesAt f (ρ₂ ^ F.q)) : ConvergesAt (F.phiSeq f) ρ :=
  convergesAt_of_bounded (F.r₀_pos.trans_le h1) h12 h2
    (phiSeq_weight_le h1 ((h12.trans h2).trans h2') hf1)
    (phiSeq_weight_le ((h1.trans h12.le).trans h2.le) h2' hf2)

theorem exists_radius_pow (f : Robba K) : ∃ s, 0 < s ∧ s < 1 ∧ ∀ ρ, s ≤ ρ → ρ < 1 →
    F.r₀ ≤ ρ ∧ ConvergesAt f.coeff (ρ ^ F.q) :=
  Robba.exists_Ico_of_eventually (eventually_r₀_le.and (eventually_convergesAt_pow f))

theorem phiSeq_exists_convergesAt (f : Robba K) :
    ∃ r < 1, ∀ ρ, r ≤ ρ → ρ < 1 → 0 < ρ → ConvergesAt (F.phiSeq f.coeff) ρ := by
  obtain ⟨s, hs0, hs1, hs⟩ := exists_radius_pow (F := F) f
  refine ⟨(s + 1) / 2, by linarith, fun ρ h1 h2 _ => ?_⟩
  obtain ⟨hr, hc1⟩ := hs s le_rfl hs1
  have hρ2 : ρ < (ρ + 1) / 2 := by linarith
  have hρ21 : (ρ + 1) / 2 < 1 := by linarith
  exact phiSeq_convergesAt hr (by linarith) hρ2 hρ21 hc1 (hs _ (by linarith) hρ21).2

variable (F) in

def phiFun (f : Robba K) : Robba K := ⟨F.phiSeq f.coeff, phiSeq_exists_convergesAt f⟩

@[simp] theorem coeff_phiFun (f : Robba K) : (F.phiFun f).coeff = F.phiSeq f.coeff := rfl

theorem exists_common_pow (f g : Robba K) : ∃ s, 0 < s ∧ s < 1 ∧ ∀ ρ, s ≤ ρ → ρ < 1 →
    F.r₀ ≤ ρ ∧ ConvergesAt f.coeff (ρ ^ F.q) ∧ ConvergesAt g.coeff (ρ ^ F.q) :=
  Robba.exists_Ico_of_eventually
    (eventually_r₀_le.and ((eventually_convergesAt_pow f).and (eventually_convergesAt_pow g)))

theorem phiSeq_add {f g : ℤ → K} (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) (hf : ConvergesAt f (ρ ^ F.q))
    (hg : ConvergesAt g (ρ ^ F.q)) : F.phiSeq (f + g) = F.phiSeq f + F.phiSeq g := by
  funext m
  simp only [phiSeq, Pi.add_apply, map_add, add_mul]
  exact (summable_phi_term h1 h2 hf m).tsum_add (summable_phi_term h1 h2 hg m)

theorem phiFun_add (f g : Robba K) : F.phiFun (f + g) = F.phiFun f + F.phiFun g := by
  obtain ⟨s, -, hs1, hs⟩ := exists_common_pow (F := F) f g
  obtain ⟨h1, hf, hg⟩ := hs s le_rfl hs1
  exact Robba.ext (phiSeq_add h1 hs1 hf hg)

theorem phiSeq_single (k : ℤ) (c : K) : F.phiSeq (Pi.single k c) = F.σ c • F.U k := by
  funext m
  simp only [phiSeq, Pi.smul_apply, smul_eq_mul]
  rw [tsum_eq_single k fun n hn => by simp [hn]]
  simp

theorem phiFun_one : F.phiFun 1 = 1 := by
  ext m
  simp [phiSeq_single, U_zero]

theorem continuous_σ : Continuous F.σ :=
  (AddMonoidHomClass.isometry_of_norm F.σ F.norm_σ).continuous

theorem norm_U_le' (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) (n m : ℤ) :
    ‖F.U n m‖ ≤ (ρ ^ F.q) ^ n * ρ ^ (-m) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have := norm_U_le h1 h2 n m
  rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (zpow_pos hρ m)]
  exact this

theorem norm_U_mul_U_le {ρ₁ ρ₂ : ℝ} (h1 : F.r₀ ≤ ρ₁) (h12 : ρ₁ < ρ₂) (h2 : ρ₂ < 1) (i k j m : ℤ) :
    ‖F.U i j‖ * ‖F.U k (m - j)‖ ≤ ((ρ₁ ^ F.q) ^ i + (ρ₂ ^ F.q) ^ i) *
      ((ρ₁ ^ F.q) ^ k + (ρ₂ ^ F.q) ^ k) * ((ρ₁ ^ (-m) + ρ₂ ^ (-m)) * (ρ₁ / ρ₂) ^ |j|) := by
  have hρ₁ : 0 < ρ₁ := F.r₀_pos.trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ₁.trans h12
  have h1' : F.r₀ ≤ ρ₂ := h1.trans h12.le
  have h2' : ρ₁ < 1 := h12.trans h2
  rcases le_total 0 j with hj | hj
  · calc ‖F.U i j‖ * ‖F.U k (m - j)‖
        ≤ ((ρ₂ ^ F.q) ^ i * ρ₂ ^ (-j)) * ((ρ₁ ^ F.q) ^ k * ρ₁ ^ (-(m - j))) :=
          mul_le_mul (norm_U_le' h1' h2 i j) (norm_U_le' h1 h2' k (m - j)) (norm_nonneg _)
            (by positivity)
      _ = (ρ₂ ^ F.q) ^ i * (ρ₁ ^ F.q) ^ k * (ρ₁ ^ (-m) * (ρ₁ / ρ₂) ^ |j|) := by
          rw [abs_of_nonneg hj, div_zpow, show -(m - j) = -m + j by ring,
            zpow_add₀ hρ₁.ne', zpow_neg ρ₂ j]
          field_simp
      _ ≤ _ := by
          gcongr
          · exact le_add_of_nonneg_left (by positivity)
          · exact le_add_of_nonneg_right (by positivity)
          · exact le_add_of_nonneg_right (by positivity)
  · calc ‖F.U i j‖ * ‖F.U k (m - j)‖
        ≤ ((ρ₁ ^ F.q) ^ i * ρ₁ ^ (-j)) * ((ρ₂ ^ F.q) ^ k * ρ₂ ^ (-(m - j))) :=
          mul_le_mul (norm_U_le' h1 h2' i j) (norm_U_le' h1' h2 k (m - j)) (norm_nonneg _)
            (by positivity)
      _ = (ρ₁ ^ F.q) ^ i * (ρ₂ ^ F.q) ^ k * (ρ₂ ^ (-m) * (ρ₁ / ρ₂) ^ |j|) := by
          rw [abs_of_nonpos hj, div_zpow, zpow_neg ρ₂ j, div_inv_eq_mul,
            show -(m - j) = -m + j by ring, zpow_add₀ hρ₂.ne']
          ring
      _ ≤ _ := by
          gcongr
          · exact le_add_of_nonneg_right (by positivity)
          · exact le_add_of_nonneg_left (by positivity)
          · exact le_add_of_nonneg_left (by positivity)

theorem tendsto_pow_abs {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    Tendsto (fun j : ℤ => t ^ |j|) cofinite (𝓝 0) := by
  rw [Int.cofinite_eq]
  refine tendsto_sup.2 ⟨?_, ?_⟩
  · refine ((tendsto_zpow_atTop_of_lt_one h0 h1).comp tendsto_neg_atBot_atTop).congr' ?_
    filter_upwards [eventually_le_atBot (0 : ℤ)] with j hj
    simp [abs_of_nonpos hj]
  · refine (tendsto_zpow_atTop_of_lt_one h0 h1).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with j hj
    simp [abs_of_nonneg hj]

theorem phiSeq_cmul {ρ₁ ρ₂ : ℝ} (h1 : F.r₀ ≤ ρ₁) (h12 : ρ₁ < ρ₂) (h2 : ρ₂ < 1) {f g : ℤ → K}
    (hf1 : ConvergesAt f (ρ₁ ^ F.q)) (hf2 : ConvergesAt f (ρ₂ ^ F.q))
    (hg1 : ConvergesAt g (ρ₁ ^ F.q)) (hg2 : ConvergesAt g (ρ₂ ^ F.q)) :
    F.phiSeq (cmul f g) = cmul (F.phiSeq f) (F.phiSeq g) := by
  have hρ₁ : 0 < ρ₁ := F.r₀_pos.trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ₁.trans h12
  have hq₁ : 0 < ρ₁ ^ F.q := by positivity
  funext m

  set T3 : (ℤ × ℤ) × ℤ → K := fun p =>
    (F.σ (f p.1.1) * F.σ (g p.1.2)) * (F.U p.1.1 p.2 * F.U p.1.2 (m - p.2)) with hT3def
  have hT3 : Summable T3 := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ha : Tendsto (fun i => ‖f i‖ * ((ρ₁ ^ F.q) ^ i + (ρ₂ ^ F.q) ^ i)) cofinite (𝓝 0) := by
      simpa [mul_add] using (show Tendsto _ _ _ from hf1).add (show Tendsto _ _ _ from hf2)
    have hb : Tendsto (fun i => ‖g i‖ * ((ρ₁ ^ F.q) ^ i + (ρ₂ ^ F.q) ^ i)) cofinite (𝓝 0) := by
      simpa [mul_add] using (show Tendsto _ _ _ from hg1).add (show Tendsto _ _ _ from hg2)
    have hc : Tendsto (fun j : ℤ => (ρ₁ ^ (-m) + ρ₂ ^ (-m)) * (ρ₁ / ρ₂) ^ |j|) cofinite (𝓝 0) := by
      simpa using (tendsto_pow_abs (by positivity) ((div_lt_one hρ₂).2 h12)).const_mul
        (ρ₁ ^ (-m) + ρ₂ ^ (-m))
    refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_)
      (tendsto_mul_cofinite_nhds_zero (tendsto_mul_cofinite_nhds_zero ha hb) hc)
    simp only [T3, norm_mul, F.norm_σ]
    have := norm_U_mul_U_le h1 h12 h2 p.1.1 p.1.2 p.2 m
    calc ‖f p.1.1‖ * ‖g p.1.2‖ * (‖F.U p.1.1 p.2‖ * ‖F.U p.1.2 (m - p.2)‖)
        ≤ ‖f p.1.1‖ * ‖g p.1.2‖ * (((ρ₁ ^ F.q) ^ p.1.1 + (ρ₂ ^ F.q) ^ p.1.1) *
            ((ρ₁ ^ F.q) ^ p.1.2 + (ρ₂ ^ F.q) ^ p.1.2) *
            ((ρ₁ ^ (-m) + ρ₂ ^ (-m)) * (ρ₁ / ρ₂) ^ |p.2|)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

  have hL : F.phiSeq (cmul f g) m = ∑' p, T3 p := by
    have hinner : ∀ n, F.σ (cmul f g n) * F.U n m = ∑' i, ∑' j, T3 ((i, n - i), j) := by
      intro n
      have hs : Summable fun i => f i * g (n - i) := hf1.summable_term hq₁ hg1 n
      have e1 : F.σ (cmul f g n) = ∑' i, F.σ (f i) * F.σ (g (n - i)) := by
        have := (hs.hasSum.map F.σ continuous_σ).tsum_eq
        simpa [cmul, Function.comp] using this.symm
      have e2 : ∀ i, F.U n m = ∑' j, F.U i j * F.U (n - i) (m - j) := fun i => by
        have := F.U_add i (n - i)
        rw [add_sub_cancel] at this
        rw [this]; rfl
      rw [e1, ← tsum_mul_right]
      refine tsum_congr fun i => ?_
      rw [e2 i, ← tsum_mul_left]
    simp only [phiSeq]
    rw [tsum_congr hinner, hT3.tsum_prod]
    let e : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun p => (p.2, p.1 - p.2), invFun := fun p => (p.1 + p.2, p.1),
        left_inv := fun p => by simp, right_inv := fun p => by simp }
    have hG : Summable fun p : ℤ × ℤ => ∑' j, T3 (p, j) := hT3.prod
    set G : ℤ × ℤ → K := fun p => ∑' j, T3 (p, j)
    have hGe : Summable fun x => G (e x) := (e.summable_iff (f := G)).2 hG
    calc ∑' (b : ℤ) (i : ℤ), ∑' j, T3 ((i, b - i), j) = ∑' (b : ℤ) (i : ℤ), G (e (b, i)) := rfl
      _ = ∑' x, G (e x) := hGe.tsum_prod.symm
      _ = ∑' p, G p := e.tsum_eq G

  have hR : cmul (F.phiSeq f) (F.phiSeq g) m = ∑' p, T3 p := by
    have hfib : ∀ j, Summable fun p : ℤ × ℤ => T3 (p, j) := fun j =>
      hT3.comp_injective (i := fun p : ℤ × ℤ => (p, j)) fun a b h => (Prod.ext_iff.1 h).1
    have hj : ∀ j, F.phiSeq f j * F.phiSeq g (m - j) = ∑' p : ℤ × ℤ, T3 (p, j) := by
      intro j
      simp only [phiSeq]
      rw [← tsum_mul_right, (hfib j).tsum_prod]
      refine tsum_congr fun i => ?_
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp only [T3]; ring
    change ∑' j, F.phiSeq f j * F.phiSeq g (m - j) = _
    rw [tsum_congr hj]
    have hsw : Summable fun x : ℤ × (ℤ × ℤ) => T3 (x.2, x.1) :=
      ((Equiv.prodComm ℤ (ℤ × ℤ)).summable_iff (f := T3)).2 hT3
    calc ∑' j, ∑' p : ℤ × ℤ, T3 (p, j) = ∑' x : ℤ × (ℤ × ℤ), T3 (x.2, x.1) := hsw.tsum_prod.symm
      _ = ∑' p, T3 p := (Equiv.prodComm ℤ (ℤ × ℤ)).tsum_eq T3
  rw [hL, hR]

theorem phiFun_mul (f g : Robba K) : F.phiFun (f * g) = F.phiFun f * F.phiFun g := by
  obtain ⟨s, -, hs1, hs⟩ := exists_common_pow (F := F) f g
  obtain ⟨h1, hf1, hg1⟩ := hs s le_rfl hs1
  obtain ⟨-, hf2, hg2⟩ := hs ((s + 1) / 2) (by linarith) (by linarith)
  exact Robba.ext (phiSeq_cmul h1 (by linarith) (by linarith) hf1 hf2 hg1 hg2)

theorem phiFun_zero : F.phiFun 0 = 0 := by
  ext m
  simp [phiSeq]

variable (F) in

def phi : Robba K →+* Robba K where
  toFun := F.phiFun
  map_one' := phiFun_one
  map_mul' := phiFun_mul
  map_zero' := phiFun_zero
  map_add' := phiFun_add

theorem coeff_phi (f : Robba K) : (F.phi f).coeff = F.phiSeq f.coeff := rfl

theorem phi_single (k : ℤ) (c : K) :
    F.phi (Robba.single k c) = Robba.single 0 (F.σ c) * ((F.uu ^ k : (Robba K)ˣ) : Robba K) := by
  ext m
  rw [coeff_phi, Robba.coeff_single, phiSeq_single, Robba.coeff_single_mul]
  simp [U]

theorem phi_const (c : K) : F.phi (Robba.single 0 c) = Robba.single 0 (F.σ c) := by
  rw [phi_single, zpow_zero, Units.val_one, mul_one]

theorem phi_T : F.phi Robba.T = F.u := by
  rw [Robba.T, phi_single, zpow_one, map_one, Robba.single_zero_one, one_mul, coe_uu]

variable (F) in

def spreadSeq (f : ℤ → K) (m : ℤ) : K := ∑' n, F.σ (f n) * (Pi.single ((F.q : ℤ) * n) (1 : K) : ℤ → K) m

theorem q_mul_injective : Function.Injective fun n : ℤ => (F.q : ℤ) * n := fun a b h => by
  have : (F.q : ℤ) ≠ 0 := by exact_mod_cast F.q_pos.ne'
  exact mul_left_cancel₀ this h

theorem spreadSeq_q_mul (f : ℤ → K) (n : ℤ) : F.spreadSeq f ((F.q : ℤ) * n) = F.σ (f n) := by
  unfold spreadSeq
  rw [tsum_eq_single n fun n' hn' => by
    have : (F.q : ℤ) * n ≠ (F.q : ℤ) * n' := fun h => hn' (q_mul_injective h).symm
    simp [this]]
  simp

theorem spreadSeq_of_forall_ne (f : ℤ → K) {m : ℤ} (hm : ∀ n, m ≠ (F.q : ℤ) * n) :
    F.spreadSeq f m = 0 := by
  unfold spreadSeq
  simp [hm]

theorem phiSeq_sub_spreadSeq_le (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (m : ℤ) :
    ‖F.phiSeq f m - F.spreadSeq f m‖ * ρ ^ m ≤ F.δ ρ * gaussNorm f (ρ ^ F.q) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have hρm : 0 < ρ ^ m := zpow_pos hρ m
  have hs2 : Summable fun n => F.σ (f n) * (Pi.single ((F.q : ℤ) * n) (1 : K) : ℤ → K) m := by
    refine summable_of_hasFiniteSupport ((Set.finite_singleton (m / F.q)).subset fun n hn => ?_)
    by_contra hne
    apply hn
    have : m ≠ (F.q : ℤ) * n := by
      rintro rfl
      apply hne
      simp [Int.mul_ediv_cancel_left _ (show (F.q : ℤ) ≠ 0 by exact_mod_cast F.q_pos.ne')]
    simp [this]
  unfold phiSeq spreadSeq
  rw [← (summable_phi_term h1 h2 hf m).tsum_sub hs2, ← le_div_iff₀ hρm]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (div_nonneg (mul_nonneg (δ_nonneg hρ) (gaussNorm_nonneg (by positivity))) hρm.le) fun n => ?_
  rw [le_div_iff₀ hρm, ← mul_sub, norm_mul, F.norm_σ, mul_assoc]
  have hd := (U_spec h1 h2 n).2
  have hdc : ConvergesAt (F.U n - Pi.single ((F.q : ℤ) * n) 1) ρ :=
    (convergesAt_U h1 h2 n).sub hρ (convergesAt_single _ _ _)
  calc ‖f n‖ * (‖F.U n m - (Pi.single ((F.q : ℤ) * n) (1 : K) : ℤ → K) m‖ * ρ ^ m)
      ≤ ‖f n‖ * (F.δ ρ * (ρ ^ F.q) ^ n) :=
        mul_le_mul_of_nonneg_left ((hdc.le_gaussNorm m).trans hd) (norm_nonneg _)
    _ = F.δ ρ * (‖f n‖ * (ρ ^ F.q) ^ n) := by ring
    _ ≤ F.δ ρ * gaussNorm f (ρ ^ F.q) :=
        mul_le_mul_of_nonneg_left (hf.le_gaussNorm n) (δ_nonneg hρ)

theorem weight_phiSeq (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (hf0 : f ≠ 0) (m : ℤ) :
    (‖F.phiSeq f m‖ * ρ ^ m = gaussNorm f (ρ ^ F.q) ↔
      ∃ n, ‖f n‖ * (ρ ^ F.q) ^ n = gaussNorm f (ρ ^ F.q) ∧ m = (F.q : ℤ) * n) ∧
    ‖F.phiSeq f m‖ * ρ ^ m ≤ gaussNorm f (ρ ^ F.q) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have hρm : 0 < ρ ^ m := zpow_pos hρ m
  set G := gaussNorm f (ρ ^ F.q)
  have hG : 0 < G := gaussNorm_pos (by positivity) hf hf0
  have hδ := δ_lt_one h1 h2
  have hsub := phiSeq_sub_spreadSeq_le h1 h2 hf m
  have hsmall : ‖F.phiSeq f m - F.spreadSeq f m‖ * ρ ^ m < G := by nlinarith [δ_nonneg (F := F) hρ]
  refine ⟨⟨fun h => ?_, ?_⟩, phiSeq_weight_le h1 h2 hf m⟩
  ·
    by_contra hne
    push Not at hne
    by_cases hm : ∃ n, m = (F.q : ℤ) * n
    · obtain ⟨n, rfl⟩ := hm
      have hlt : ‖f n‖ * (ρ ^ F.q) ^ n < G := lt_of_le_of_ne (hf.le_gaussNorm n) fun h' => hne n h' rfl
      have e : (ρ ^ F.q) ^ n = ρ ^ ((F.q : ℤ) * n) := by rw [zpow_mul, zpow_natCast]
      rw [spreadSeq_q_mul] at hsmall
      have : ‖F.phiSeq f ((F.q : ℤ) * n)‖ * ρ ^ ((F.q : ℤ) * n) < G := by
        have h3 := IsUltrametricDist.norm_add_le_max (F.phiSeq f ((F.q : ℤ) * n) - F.σ (f n))
          (F.σ (f n))
        rw [sub_add_cancel, F.norm_σ] at h3
        calc ‖F.phiSeq f ((F.q : ℤ) * n)‖ * ρ ^ ((F.q : ℤ) * n)
            ≤ max ‖F.phiSeq f ((F.q : ℤ) * n) - F.σ (f n)‖ ‖f n‖ * ρ ^ ((F.q : ℤ) * n) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = max (‖F.phiSeq f ((F.q : ℤ) * n) - F.σ (f n)‖ * ρ ^ ((F.q : ℤ) * n))
                (‖f n‖ * ρ ^ ((F.q : ℤ) * n)) := max_mul_of_nonneg _ _ (by positivity)
          _ < G := max_lt hsmall (by rw [← e]; exact hlt)
      linarith
    · push Not at hm
      rw [spreadSeq_of_forall_ne f hm, sub_zero] at hsmall
      linarith
  · rintro ⟨n, hn, rfl⟩
    have e : (ρ ^ F.q) ^ n = ρ ^ ((F.q : ℤ) * n) := by rw [zpow_mul, zpow_natCast]
    rw [spreadSeq_q_mul] at hsmall
    have hsn : ‖F.σ (f n)‖ * ρ ^ ((F.q : ℤ) * n) = G := by rw [F.norm_σ, ← e, hn]
    have hlt : ‖F.phiSeq f ((F.q : ℤ) * n) - F.σ (f n)‖ < ‖F.σ (f n)‖ := by
      rw [← mul_lt_mul_iff_of_pos_right (zpow_pos hρ ((F.q : ℤ) * n)), hsn]; exact hsmall
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le] at this
    rw [this, hsn]

theorem gaussNorm_phiSeq (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) : gaussNorm (F.phiSeq f) ρ = gaussNorm f (ρ ^ F.q) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  by_cases hf0 : f = 0
  · subst hf0
    have : F.phiSeq 0 = 0 := by funext m; simp [phiSeq]
    rw [this, gaussNorm_zero, gaussNorm_zero]
  refine le_antisymm (gaussNorm_le (phiSeq_weight_le h1 h2 hf)) ?_
  obtain ⟨n, hn⟩ := hf.exists_eq_gaussNorm (by positivity) hf0
  have := ((weight_phiSeq h1 h2 hf hf0 ((F.q : ℤ) * n)).1).2 ⟨n, hn, rfl⟩
  rw [← this]
  exact le_ciSup ⟨_, Set.forall_mem_range.2 (phiSeq_weight_le h1 h2 hf)⟩ _

theorem domSet_phiSeq (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (hf0 : f ≠ 0) :
    domSet (F.phiSeq f) ρ = (fun n => (F.q : ℤ) * n) '' domSet f (ρ ^ F.q) := by
  ext m
  simp only [domSet, Set.mem_ofPred_eq, Set.mem_image, gaussNorm_phiSeq h1 h2 hf]
  rw [(weight_phiSeq h1 h2 hf hf0 m).1]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩

theorem phiSeq_ne_zero (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (hf0 : f ≠ 0) : F.phiSeq f ≠ 0 := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  intro h
  have := gaussNorm_phiSeq h1 h2 hf
  rw [h, gaussNorm_zero] at this
  exact (gaussNorm_pos (by positivity) hf hf0).ne' this.symm

theorem lowIndex_phiSeq (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (hφ : ConvergesAt (F.phiSeq f) ρ) (hf0 : f ≠ 0) :
    lowIndex (F.phiSeq f) ρ = (F.q : ℤ) * lowIndex f (ρ ^ F.q) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have hρq : 0 < ρ ^ F.q := by positivity
  have hφ0 := phiSeq_ne_zero h1 h2 hf hf0
  have hD := domSet_phiSeq h1 h2 hf hf0
  have hq : (0 : ℤ) < F.q := by exact_mod_cast F.q_pos
  refine le_antisymm (lowIndex_le hρ hφ hφ0 ?_) ?_
  · rw [hD]; exact ⟨_, lowIndex_mem hρq hf hf0, rfl⟩
  · have hm := lowIndex_mem hρ hφ hφ0
    rw [hD] at hm
    obtain ⟨n, hn, he⟩ := hm
    rw [← he]
    exact mul_le_mul_of_nonneg_left (lowIndex_le hρq hf hf0 hn) hq.le

theorem highIndex_phiSeq (h1 : F.r₀ ≤ ρ) (h2 : ρ < 1) {f : ℤ → K}
    (hf : ConvergesAt f (ρ ^ F.q)) (hφ : ConvergesAt (F.phiSeq f) ρ) (hf0 : f ≠ 0) :
    highIndex (F.phiSeq f) ρ = (F.q : ℤ) * highIndex f (ρ ^ F.q) := by
  have hρ : 0 < ρ := F.r₀_pos.trans_le h1
  have hρq : 0 < ρ ^ F.q := by positivity
  have hφ0 := phiSeq_ne_zero h1 h2 hf hf0
  have hD := domSet_phiSeq h1 h2 hf hf0
  have hq : (0 : ℤ) < F.q := by exact_mod_cast F.q_pos
  refine le_antisymm ?_ (le_highIndex hρ hφ hφ0 ?_)
  · have hm := highIndex_mem hρ hφ hφ0
    rw [hD] at hm
    obtain ⟨n, hn, he⟩ := hm
    rw [← he]
    exact mul_le_mul_of_nonneg_left (le_highIndex hρq hf hf0 hn) hq.le
  · rw [hD]; exact ⟨_, highIndex_mem hρq hf hf0, rfl⟩

theorem eventually_phi (f : Robba K) : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), F.r₀ ≤ ρ ∧ ρ < 1 ∧
    ConvergesAt f.coeff (ρ ^ F.q) ∧ ConvergesAt (F.phi f).coeff ρ :=
  eventually_r₀_le.and ((eventually_mem_nhdsWithin (s := Set.Iio 1)).and
    ((eventually_convergesAt_pow f).and (F.phi f).eventually_convergesAt))

theorem eventually_gaussNorm_phi (f : Robba K) :
    ∀ᶠ ρ in 𝓝[<] (1 : ℝ), gaussNorm (F.phi f).coeff ρ = gaussNorm f.coeff (ρ ^ F.q) :=
  (eventually_phi f).mono fun _ h => gaussNorm_phiSeq h.1 h.2.1 h.2.2.1

theorem eventually_lowIndex_phi {f : Robba K} (hf : f ≠ 0) :
    ∀ᶠ ρ in 𝓝[<] (1 : ℝ), lowIndex (F.phi f).coeff ρ = (F.q : ℤ) * lowIndex f.coeff (ρ ^ F.q) ∧
      highIndex (F.phi f).coeff ρ = (F.q : ℤ) * highIndex f.coeff (ρ ^ F.q) := by
  have hf0 : f.coeff ≠ 0 := fun h => hf (Robba.ext h)
  exact (eventually_phi f).mono fun _ h =>
    ⟨lowIndex_phiSeq h.1 h.2.1 h.2.2.1 h.2.2.2 hf0, highIndex_phiSeq h.1 h.2.1 h.2.2.1 h.2.2.2 hf0⟩

theorem phi_injective : Function.Injective F.phi := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hne
  have hf0 : f.coeff ≠ 0 := fun h => hne (Robba.ext h)
  obtain ⟨ρ, h⟩ := (eventually_phi (F := F) f).exists
  exact phiSeq_ne_zero h.1 h.2.1 h.2.2.1 hf0 (congrArg Robba.coeff hf)

theorem norm_U_le_one (n m : ℤ) : ‖F.U n m‖ ≤ 1 := by
  have hc : ContinuousAt (fun ρ : ℝ => (ρ ^ F.q) ^ n * ρ ^ (-m)) 1 :=
    ((continuousAt_id.pow F.q).zpow₀ n (Or.inl (by simp))).mul
      (continuousAt_id.zpow₀ (-m) (Or.inl one_ne_zero))
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
  simp only [one_pow, one_zpow, mul_one] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [eventually_r₀_le (F := F), eventually_mem_nhdsWithin] with ρ h1 h2
  exact norm_U_le' h1 h2 n m

theorem phi_mem_bounded {f : Robba K} (hf : f ∈ Robba.bounded K) : F.phi f ∈ Robba.bounded K := by
  refine ⟨Robba.norm1 f, Set.forall_mem_range.2 fun m => ?_⟩
  change ‖F.phiSeq f.coeff m‖ ≤ _
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (Robba.gaussNorm_nonneg_alt f) fun n => ?_
  rw [norm_mul, F.norm_σ]
  calc ‖f.coeff n‖ * ‖F.U n m‖ ≤ Robba.norm1 f * 1 :=
        mul_le_mul (Robba.norm_coeff_le_norm1 hf n) (norm_U_le_one n m) (norm_nonneg _)
          (Robba.gaussNorm_nonneg_alt f)
    _ = _ := mul_one _

theorem gaussNorm_phi {f : Robba K} (hf : f ∈ Robba.bounded K) :
    Robba.norm1 (F.phi f) = Robba.norm1 f := by
  have h1 := Robba.tendsto_gaussNorm_norm1 (phi_mem_bounded (F := F) hf)
  have h2 := (Robba.tendsto_gaussNorm_norm1 hf).comp (tendsto_pow_q (F := F))
  exact tendsto_nhds_unique h1 (h2.congr' ((eventually_gaussNorm_phi f).mono fun _ h => h.symm))

variable (F) in

def phiBounded : Robba.bounded K →+* Robba.bounded K :=
  (F.phi.comp (Robba.bounded K).subtype).codRestrict (Robba.bounded K) fun f => phi_mem_bounded f.2

@[simp] theorem coe_phiBounded (f : Robba.bounded K) : (F.phiBounded f : Robba K) = F.phi f := rfl

end FrobeniusLift

end GroundTheory.PAdicHodge
