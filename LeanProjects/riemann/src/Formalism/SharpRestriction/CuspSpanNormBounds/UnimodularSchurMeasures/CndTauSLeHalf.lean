import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDefs

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cnd_two_le_Y (X : CData) {n₀ : ℕ} {A : ℝ} (h1 : 1 ≤ n₀) (hX : X.HypB n₀ A) : 2 ≤ cn_Y X := by
  have hn : 1 ≤ X.I.n := le_trans h1 hX.1.1
  have hg1 : (1 : ℝ) ≤ (X.g : ℝ) := by exact_mod_cast hX.1.2.2.2.2.2.2.2.1
  have h := two_mul_le_height_parameter (n := X.I.n) (f := X.I.f) hn (one_le_autInst_f X.I) (one_le_discriminant_root X.I) hg1 hX.1.2.2.1
  have hnR : (1 : ℝ) ≤ (X.I.n : ℝ) := by exact_mod_cast hn
  unfold cn_Y
  linarith

theorem cnd_tauS_pos (X : CData) (C₁ : ℝ) (hY : 2 ≤ cn_Y X) : 0 < cn_tauS X C₁ :=
  Real.rpow_pos_of_pos (by linarith) _

theorem cnd_tauS_le_half (X : CData) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) (hq : 1 ≤ X.qq) (hY : 2 ≤ cn_Y X) :
    cn_tauS X C₁ ≤ 1 / 2 := by
  have hqR : (1 : ℝ) ≤ (X.qq : ℝ) := by exact_mod_cast hq
  have h1 : (1 : ℝ) ≤ C₁ * (X.qq : ℝ) := by nlinarith
  have h2 : cn_tauS X C₁ ≤ cn_Y X ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h3 : cn_Y X ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) hY
  exact le_trans h2 h3

theorem cnd_tauS_anti (X : CData) {C₁ C₁' : ℝ} (h : C₁ ≤ C₁') (hY : 2 ≤ cn_Y X) :
    cn_tauS X C₁' ≤ cn_tauS X C₁ := by
  have hq : (0 : ℝ) ≤ (X.qq : ℝ) := Nat.cast_nonneg _
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)

theorem cnd_tauS_zero (X : CData) (C₁ : ℝ) (hq : X.qq = 0) : cn_tauS X C₁ = 1 := by
  unfold cn_tauS
  rw [hq]
  simp

theorem cnd_Mod_zero {X : CData} (S : CSize X) (hst : S.Strata) (C₁ : ℝ) (hq : X.qq = 0) : S.Mod C₁ = ∅ := by
  ext x
  simp only [CSize.Mod, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
  rw [cnd_tauS_zero X C₁ hq]
  have := (hst.2.2.2.2.2.1 x).2
  linarith

def CSize.PackCount {X : CData} (S : CSize X) : Prop :=
  ∀ x : X.I.GA, ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ T : Finset X.I.GFset,
    (∀ γ ∈ T, X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 ∧ ∀ v, X.dist x γ v ≤ r v) →
    (T.card : ℝ) ≤
      (1 + 2 * (∏ v, Real.sqrt (X.I.n : ℝ) * Real.exp (r v)) ^ (1 / (Fintype.card (InfinitePlace X.I.F) : ℝ)) /
        S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F))

theorem cnd_far {X : CData} (S : CSize X) (C₁ : ℝ) (hn : 1 ≤ X.I.n) (hY : 2 ≤ cn_Y X) (hst : S.Strata)
    (hP : S.PackCount) : X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) (S.Mod C₁) := by
  intro x hx r hr T hT
  have hτ := hst.2.2.2.2.2.1 x
  have hs : (1 : ℝ) ≤ Real.sqrt (X.I.n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have h1 := hP x r hr T hT
  have h2 := Formalism.HermitianLatticeCounting.Final.S7.farCount (InfinitePlace X.I.F) X.I.n r (S.tau1 x) (Real.sqrt (X.I.n : ℝ)) hτ.1
    (by linarith [hτ.2]) hs hr
  have hτs : 0 < cn_tauS X C₁ := cnd_tauS_pos X C₁ hY
  have hle : cn_tauS X C₁ ≤ S.tau1 x := hx
  have hsq : cn_tauS X C₁ ^ 2 ≤ S.tau1 x ^ 2 := pow_le_pow_left₀ hτs.le hle 2
  have hsq1 : cn_tauS X C₁ ^ 2 ≤ 1 := by
    have : cn_tauS X C₁ ≤ 1 := by linarith [hτ.2]
    exact pow_le_one₀ hτs.le this
  have hbase : 3 * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2 ≤ 3 * Real.sqrt (X.I.n : ℝ) / cn_tauS X C₁ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
  have hbase1 : 1 ≤ 3 * Real.sqrt (X.I.n : ℝ) / cn_tauS X C₁ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hA : (3 * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F)) ≤
      X.Acnt C₁ := by
    have e1 : (3 * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F)) ≤
        (3 * Real.sqrt (X.I.n : ℝ) / cn_tauS X C₁ ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F)) :=
      pow_le_pow_left₀ (by have := hτ.1; positivity) hbase _
    have e2 : (3 * Real.sqrt (X.I.n : ℝ) / cn_tauS X C₁ ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F)) ≤
        (3 * Real.sqrt (X.I.n : ℝ) / cn_tauS X C₁ ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f) :=
      pow_le_pow_right₀ hbase1 (Nat.mul_le_mul_left _ (card_infinite_places_le_degree X.I))
    exact le_trans e1 e2
  calc (T.card : ℝ) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ X.Acnt C₁ * Real.exp (2 * (X.I.n : ℝ) ^ 2 * ∑ v, r v) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le

theorem cnd_far_zero (X : CData) (C₁ : ℝ) (hn : 1 ≤ X.I.n) (hq : X.qq = 0) (Mod : Set X.I.GA)
    (hN : ∀ x ∈ Mod, ∀ γ : X.I.GFset, X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 → γ = X.one') :
    X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod := by
  intro x hx r hr T hT
  have hs : (1 : ℝ) ≤ Real.sqrt (X.I.n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hc : T.card ≤ 1 := Finset.card_le_one.2 fun a ha b hb => by
    rw [hN x hx a (hT a ha).1, hN x hx b (hT b hb).1]
  have hA : 1 ≤ X.Acnt C₁ := by
    unfold CData.Acnt
    rw [hq]
    apply one_le_pow₀
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, one_pow, div_one]
    linarith
  have hE : 1 ≤ Real.exp (2 * (X.I.n : ℝ) ^ 2 * ∑ v, r v) :=
    Real.one_le_exp (mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ => hr v))
  calc (T.card : ℝ) ≤ 1 := by exact_mod_cast hc
    _ ≤ X.Acnt C₁ * Real.exp (2 * (X.I.n : ℝ) ^ 2 * ∑ v, r v) := by nlinarith

theorem cnd_deep_int (X : CData) (hV : X.FinVol) {Mod : Set X.I.GA} (hM : MeasurableSet Mod)
    (key : ∀ᵐ x ∂X.μ, x ∈ Modᶜ →
      X.I.vol X.μf X.fund * |(X.kerD x).re| ≤ X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))))
    {A₁ : ℝ} (hA₁ : 1 ≤ A₁) : X.DeepInt A₁ Mod := by
  have hD : 0 ≤ X.Dc := Nat.cast_nonneg _
  have hE := Real.exp_pos (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)))
  have hfin : X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) ≤
      A₁ * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) * X.Dc := by
    have : 0 ≤ X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) := mul_nonneg hD hE.le
    nlinarith
  have : IsFiniteMeasure X.μ := ⟨by
    unfold CData.μ
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hV⟩
  have hvol := X.vol_eq
  unfold CData.DeepInt
  refine le_trans ?_ hfin
  by_cases hv0 : X.I.vol X.μf X.fund = 0
  · have hμ0 : X.μ.real (Modᶜ) = 0 := by
      have h1 : X.μ.real (Modᶜ) ≤ X.μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      rw [← hvol, hv0] at h1
      exact le_antisymm h1 measureReal_nonneg
    have hz : X.μ (Modᶜ) = 0 := by
      rcases (measureReal_eq_zero_iff (μ := X.μ) (s := Modᶜ)).1 hμ0 with h
      exact h
    rw [Measure.restrict_eq_zero.2 hz, integral_zero_measure, abs_zero]
    exact mul_nonneg hD hE.le
  · have hvpos : 0 < X.I.vol X.μf X.fund :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hv0)
    have hb : ∀ᵐ x ∂(X.μ.restrict Modᶜ), ‖(X.kerD x).re‖ ≤
        X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) / X.I.vol X.μf X.fund := by
      rw [ae_restrict_iff' hM.compl]
      filter_upwards [key] with x hx hxM
      rw [le_div_iff₀ hvpos, Real.norm_eq_abs, mul_comm]
      exact hx hxM
    have h1 := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at h1
    refine le_trans h1 ?_
    have h2 : (X.μ.restrict Modᶜ).real Set.univ ≤ X.I.vol X.μf X.fund := by
      rw [hvol, measureReal_restrict_apply_univ]
      exact measureReal_mono (Set.subset_univ _)
    have h3 : 0 ≤ X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) / X.I.vol X.μf X.fund :=
      div_nonneg (mul_nonneg hD hE.le) hvpos.le
    calc _ ≤ X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) / X.I.vol X.μf X.fund * X.I.vol X.μf X.fund :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by field_simp

theorem cnd_deep_zero (X : CData) {A₁ : ℝ} (hA₁ : 0 ≤ A₁) : X.DeepInt A₁ Set.univ := by
  unfold CData.DeepInt
  rw [Set.compl_univ, Measure.restrict_empty, integral_zero_measure, abs_zero]
  have hD : 0 ≤ X.Dc := Nat.cast_nonneg _
  have := Real.exp_pos (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)))
  positivity

structure CDeep (X : CData) where
  theta : X.I.GA → ℝ
  rho : X.I.GA → ℝ
  Bs : X.I.GA → ℝ
  volK : ℝ

def CSize.DeepStepsY {X : CData} (S : CSize X) (T : CDeep X) (Cd : ℝ) : Prop :=
  0 < T.volK ∧ X.I.vol X.μf X.fund / T.volK ≤ cn_Y X ^ (Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      0 ≤ T.theta x ∧ T.theta x ≤ cn_Y X ^ Cd * (2 * S.tau1 x) ^ (1 / (X.qq : ℝ)) ∧
      |(X.kerD x).re| ≤ T.theta x ^ (2 * Formalism.HermitianLatticeCounting.S7.P0 X.I.n X.qq X.I.f) * T.Bs x ∧
      T.Bs x ≤ cn_Y X ^ (Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) * (1 / S.tau1 x) ^ (4 * X.I.n ^ 2 * X.I.f) * X.Dc / T.volK

theorem cnd_deepY (Cd : ℝ) (hCd : 0 ≤ Cd) : ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ C₁ ≥ C₁₀, ∀ (X : CData) (S : CSize X) (T : CDeep X),
    1 ≤ X.qq → 2 ≤ cn_Y X → X.FinVol → S.Strata → S.DeepStepsY T Cd → ∀ A₁ : ℝ, 1 ≤ A₁ → X.DeepInt A₁ (S.Mod C₁) := by
  obtain ⟨C₁₀, h1, hB⟩ := Formalism.HermitianLatticeCounting.Final.S7.deepBoundY Cd hCd
  refine ⟨C₁₀, h1, fun C₁ hC₁ X S T hq hY hV hst hS A₁ hA₁ => ?_⟩
  obtain ⟨hvK, hvol, hae⟩ := hS
  have hD : 0 ≤ X.Dc := Nat.cast_nonneg _
  have hτs := cnd_tauS_pos X C₁ hY
  refine cnd_deep_int X hV (S.measurableSet_Mod hst C₁) ?_ hA₁
  filter_upwards [hae] with x hx hxM
  have hlt : S.tau1 x < cn_tauS X C₁ := not_le.1 hxM
  obtain ⟨a, b, c, d⟩ := hx (lt_of_lt_of_le hlt (cnd_tauS_le_half X (le_trans h1 hC₁) hq hY))
  have h2 := Formalism.HermitianLatticeCounting.Final.S7.deepChainY Cd X.I.n X.qq X.I.f (cn_Y X) (S.tau1 x) (cn_tauS X C₁) (T.theta x)
    |(X.kerD x).re| (T.Bs x) X.Dc (X.I.vol X.μf X.fund) T.volK hCd hq hY (hst.2.2.2.2.2.1 x).1 hlt hD hvK
    ENNReal.toReal_nonneg a b c d hvol
  have h3 := hB X.I.n X.qq X.I.f (cn_Y X) hq hY
  have h4 : cn_tauS X C₁ ^ (12 * X.I.n ^ 2 * X.I.f) ≤ (cn_Y X ^ (-(C₁₀ * (X.qq : ℝ)))) ^ (12 * X.I.n ^ 2 * X.I.f) :=
    pow_le_pow_left₀ hτs.le (cnd_tauS_anti X hC₁ hY) _
  have hYp : 0 ≤ cn_Y X ^ ((16 * (X.qq : ℝ) * Cd + 2 * Cd + 16) * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) :=
    Real.rpow_nonneg (by linarith) _
  calc _ ≤ _ := h2
    _ = X.Dc * (cn_Y X ^ ((16 * (X.qq : ℝ) * Cd + 2 * Cd + 16) * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
          cn_tauS X C₁ ^ (12 * X.I.n ^ 2 * X.I.f)) := by ring
    _ ≤ X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left h4 hYp) h3) hD

def CSize.DeepStepsV {X : CData} (S : CSize X) (T : CDeep X) (Cd : ℝ) : Prop :=
  0 < T.volK ∧ X.I.vol X.μf X.fund / T.volK ≤ cn_Y X ^ (Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      0 ≤ T.rho x ∧
      T.rho x ≤ Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * (X.g : ℝ) * X.I.rd * (2 * S.tau1 x) ^ (1 / (X.qq : ℝ)) ∧
      |(X.kerD x).re| ≤ (Cd * T.rho x * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * Formalism.HermitianLatticeCounting.S7.b1 X.I.n X.qq X.I.f X.b) ^
          (2 * Formalism.HermitianLatticeCounting.S7.P0 X.I.n X.qq X.I.f) * T.Bs x ∧
      T.Bs x ≤ X.Dc * T.volK⁻¹ * (Cd * (X.I.n : ℝ) ^ 2 * Formalism.HermitianLatticeCounting.S7.b1 X.I.n X.qq X.I.f X.b) ^ (X.I.n ^ 2 * X.I.f) *
          (Cd / S.tau1 x) ^ (4 * X.I.n ^ 2 * X.I.f)

theorem cnd_deepV (Cd : ℝ) (hCd : 1 ≤ Cd) : ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ C₁ ≥ C₁₀, ∀ (X : CData) (S : CSize X) (T : CDeep X)
    (n₀ : ℕ) (A : ℝ), 1 ≤ n₀ → X.HypB n₀ A → 1 ≤ X.qq → X.FinVol → S.Strata → S.DeepStepsV T Cd →
    ∀ A₁ : ℝ, 1 ≤ A₁ → X.DeepInt A₁ (S.Mod C₁) := by
  obtain ⟨C', hC', hch⟩ := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.deepChainV Cd hCd
  obtain ⟨C₁₀, h1, hB⟩ := Formalism.HermitianLatticeCounting.Final.S7.deepBound C' hC'
  refine ⟨C₁₀, h1, fun C₁ hC₁ X S T n₀ A hn₀ hX hq hV hst hS A₁ hA₁ => ?_⟩
  obtain ⟨hvK, hvol, hae⟩ := hS
  have hY := cnd_two_le_Y X hn₀ hX
  have hn : 1 ≤ X.I.n := le_trans hn₀ hX.1.1
  have hg1 : (1 : ℝ) ≤ (X.g : ℝ) := by exact_mod_cast hX.1.2.2.2.2.2.2.2.1
  have hb : 2 ≤ X.b := hX.1.2.2.1
  have hq2 := (X.qq_spec hX).2
  have hD : 0 ≤ X.Dc := Nat.cast_nonneg _
  have hτs := cnd_tauS_pos X C₁ hY
  refine cnd_deep_int X hV (S.measurableSet_Mod hst C₁) ?_ hA₁
  filter_upwards [hae] with x hx hxM
  have hlt : S.tau1 x < cn_tauS X C₁ := not_le.1 hxM
  obtain ⟨a, b, c, d⟩ := hx (lt_of_lt_of_le hlt (cnd_tauS_le_half X (le_trans h1 hC₁) hq hY))
  have h2 := hch X.I.n X.qq X.I.f X.I.rd (X.g : ℝ) X.b (S.tau1 x) (cn_tauS X C₁) (T.rho x)
    |(X.kerD x).re| (T.Bs x) X.Dc (X.I.vol X.μf X.fund) T.volK hn hq hq2 (one_le_autInst_f X.I) (one_le_discriminant_root X.I) hg1 hb
    (hst.2.2.2.2.2.1 x).1 hlt hD hvK ENNReal.toReal_nonneg a b c d hvol
  have h3 := hB X.I.n X.qq X.I.f X.I.rd (X.g : ℝ) X.b hn hq hq2 (one_le_autInst_f X.I) (one_le_discriminant_root X.I) hg1 hb
  have h4 : cn_tauS X C₁ ^ (12 * X.I.n ^ 2 * X.I.f) ≤
      (Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b ^ (-(C₁₀ * (X.qq : ℝ)))) ^ (12 * X.I.n ^ 2 * X.I.f) :=
    pow_le_pow_left₀ hτs.le (cnd_tauS_anti X hC₁ hY) _
  have hb1 : 0 ≤ Formalism.HermitianLatticeCounting.S7.b1 X.I.n X.qq X.I.f X.b := by
    unfold Formalism.HermitianLatticeCounting.S7.b1
    positivity
  have hrd0 : 0 ≤ X.I.rd := le_trans zero_le_one (one_le_discriminant_root X.I)
  have hYp : 0 ≤ Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b ^ (C' * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
      (C' * (X.I.n : ℝ) ^ 4 * (X.I.f : ℝ) ^ 2 * (X.g : ℝ) * X.I.rd * Formalism.HermitianLatticeCounting.S7.b1 X.I.n X.qq X.I.f X.b) ^
        (16 * X.qq * X.I.n ^ 2 * X.I.f) := by
    have h0 : 0 ≤ Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b := by
      have : 2 ≤ Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b := hY
      linarith
    have hC0 : 0 ≤ C' := by linarith
    exact mul_nonneg (Real.rpow_nonneg h0 _) (pow_nonneg (by positivity) _)
  calc _ ≤ _ := h2
    _ = X.Dc * (Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b ^ (C' * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
          (C' * (X.I.n : ℝ) ^ 4 * (X.I.f : ℝ) ^ 2 * (X.g : ℝ) * X.I.rd * Formalism.HermitianLatticeCounting.S7.b1 X.I.n X.qq X.I.f X.b) ^
            (16 * X.qq * X.I.n ^ 2 * X.I.f) * cn_tauS X C₁ ^ (12 * X.I.n ^ 2 * X.I.f)) := by ring
    _ ≤ X.Dc * Real.exp (-((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left h4 hYp) h3) hD

theorem cnd_volRatio (X : CData) {n₀ : ℕ} {A : ℝ} (hn₀ : 1 ≤ n₀) (hX : X.HypB n₀ A) (C volK : ℝ) (hK : 0 < volK)
    (h1 : X.I.vol X.μf X.fund ≤ cn_Y X ^ (C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)))
    (h2 : volK⁻¹ ≤ (X.g : ℝ) ^ (2 * X.I.n ^ 2 * X.I.f)) :
    X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ ((C + 2) * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) :=
  Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.volLevel C X.I.n X.I.f X.I.rd (X.g : ℝ) X.b _ volK (le_trans hn₀ hX.1.1) (one_le_autInst_f X.I)
    (one_le_discriminant_root X.I) (by exact_mod_cast hX.1.2.2.2.2.2.2.2.1) hX.1.2.2.1 hK h1 h2

end Formalism.MainNotions.LeviCoordinates

end
