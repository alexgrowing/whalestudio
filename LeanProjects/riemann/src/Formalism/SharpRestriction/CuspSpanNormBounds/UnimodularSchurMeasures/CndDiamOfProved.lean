import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndDiamOfKnown

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (P0 b1 Ydat)

theorem cnd_cov_of_proved (n f : ℕ) (hf : 1 ≤ f) (rd ρ₀ : ℝ) (hrd : 0 < rd) (hρ₀ : 0 < ρ₀)
    (P : ℝ → Prop) (hP : ∀ R R', R ≤ R' → P R → P R')
    (h : cnd_CovLe (2 * n ^ 2 * f) (Real.sqrt (f : ℝ) / (2 * rd * ρ₀)) P) :
    P (8 * (n : ℝ) ^ 6 * (f : ℝ) ^ ((5 : ℝ) / 2) * rd * ρ₀) := by
  obtain ⟨V, i1, i2, i3, M, hd, hsp, hN, hdual, hR⟩ := h
  have hκ : 0 < Real.sqrt (f : ℝ) / (2 * rd * ρ₀) :=
    div_pos (Real.sqrt_pos.2 (by exact_mod_cast hf)) (by positivity)
  have h1 := Formalism.HermitianLatticeCounting.Final.S7.coverRadius V M hd hsp _ hκ hdual
  have h2 := (Formalism.HermitianLatticeCounting.Final.S7.coverArith n f (Module.finrank ℝ V) rd ρ₀ hf hN hrd hρ₀).2.2
  exact hP _ _ h2 (hR _ h1)

theorem cnd_diam_of_proved (X : CData) (Cq ρ ρ₀ : ℝ) (hCq : 0 ≤ Cq) (hρ₀ : 0 < ρ₀) (h : cnd_Diam X Cq ρ ρ₀) :
    ρ ≤ (16 * Cq) * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * ((X.g : ℝ) * (X.I.n : ℝ) ^ 4 * (X.I.f : ℝ) ^ 2) * X.I.rd * ρ₀ := by
  have hrd : 0 < X.I.rd := lt_of_lt_of_le zero_lt_one (one_le_discriminant_root X.I)
  have hco : 0 ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) := by positivity
  have hmono2 : ∀ R₁ R R' : ℝ, R ≤ R' → ρ ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * (R₁ + R) →
      ρ ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * (R₁ + R') := fun R₁ R R' hRR h =>
    le_trans h (mul_le_mul_of_nonneg_left (by linarith) hco)
  have h1 := cnd_cov_of_proved X.I.n X.I.f (one_le_autInst_f X.I) X.I.rd ρ₀ hrd hρ₀ _ (by
    intro R R' hRR hh
    obtain ⟨V, i1, i2, i3, M, hd, hsp, hN, hdual, hR⟩ := hh
    exact ⟨V, i1, i2, i3, M, hd, hsp, hN, hdual, fun R₂ hc =>
      le_trans (hR R₂ hc) (mul_le_mul_of_nonneg_left (by linarith) hco)⟩) h
  have h2 := cnd_cov_of_proved X.I.n X.I.f (one_le_autInst_f X.I) X.I.rd ρ₀ hrd hρ₀ _ (hmono2 _) h1
  have hf0 : (0 : ℝ) < (X.I.f : ℝ) := by exact_mod_cast one_le_autInst_f X.I
  have hs : Real.sqrt (X.I.f : ℝ) * (X.I.f : ℝ) ^ ((5 : ℝ) / 2) = (X.I.f : ℝ) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hf0, ← Real.rpow_natCast]
    norm_num
  calc ρ ≤ _ := h2
    _ = (16 * Cq) * (X.I.n : ℝ) ^ 6 * (Real.sqrt (X.I.f : ℝ) * (X.I.f : ℝ) ^ ((5 : ℝ) / 2)) * (X.g : ℝ) * X.I.rd * ρ₀ := by ring
    _ = _ := by rw [hs]; ring

theorem cnd_pointG (Cd : ℝ) (hCd : 1 ≤ Cd) : ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ (n q f : ℕ) (rd g b τ₁ τs ρ Kxx Bs D volG volK : ℝ),
    1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f → 1 ≤ rd → 1 ≤ g → 2 ≤ b → 0 < τ₁ → τ₁ < τs →
    τs ≤ Ydat n f rd g b ^ (-(C₁₀ * (q : ℝ))) → 0 ≤ D → 0 < volK → 0 ≤ volG → 0 ≤ ρ →
    ρ ≤ Cd * (n : ℝ) ^ 2 * (f : ℝ) * g * rd * (2 * τ₁) ^ (1 / (q : ℝ)) →
    Kxx ≤ (Cd * ρ * (n : ℝ) ^ 2 * (f : ℝ) * b1 n q f b) ^ (2 * P0 n q f) * Bs →
    Bs ≤ D * volK⁻¹ * (Cd * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * (Cd / τ₁) ^ (4 * n ^ 2 * f) →
    volG / volK ≤ Ydat n f rd g b ^ (Cd * (n : ℝ) ^ 2 * (f : ℝ)) →
    volG * Kxx ≤ D * Real.exp (-((n : ℝ) ^ 2 * (f : ℝ))) := by
  obtain ⟨C', hC', hch⟩ := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.deepChainV Cd hCd
  obtain ⟨C₁₀, h1, hB⟩ := Formalism.HermitianLatticeCounting.Final.S7.deepBound C' hC'
  refine ⟨C₁₀, h1, fun n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hq2 hf hrd hg hb hτ hlt hτs hD hvK hvG a b' c d
    hvol => ?_⟩
  have h2 := hch n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hq2 hf hrd hg hb hτ hlt hD hvK hvG a b' c d hvol
  have h3 := hB n q f rd g b hn hq hq2 hf hrd hg hb
  have h4 : τs ^ (12 * n ^ 2 * f) ≤ (Ydat n f rd g b ^ (-(C₁₀ * (q : ℝ)))) ^ (12 * n ^ 2 * f) :=
    pow_le_pow_left₀ (le_trans hτ.le hlt.le) hτs _
  have hb1 : 0 ≤ b1 n q f b := by
    unfold Formalism.HermitianLatticeCounting.S7.b1
    positivity
  have hY0 : 0 ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    positivity
  have hYp : 0 ≤ Ydat n f rd g b ^ (C' * (n : ℝ) ^ 2 * (f : ℝ)) *
      (C' * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f) := by
    have hC0 : 0 ≤ C' := by linarith
    exact mul_nonneg (Real.rpow_nonneg hY0 _) (pow_nonneg (by positivity) _)
  calc _ ≤ _ := h2
    _ = D * (Ydat n f rd g b ^ (C' * (n : ℝ) ^ 2 * (f : ℝ)) *
          (C' * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f) * τs ^ (12 * n ^ 2 * f)) := by ring
    _ ≤ D * Real.exp (-((n : ℝ) ^ 2 * (f : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left h4 hYp) h3) hD

theorem cnd_Y' (n f : ℕ) (rd g b : ℝ) (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g) (hb : 2 ≤ b) :
    Ydat n f rd g b ≤ Ydat n f rd (g * (n : ℝ) ^ 4 * (f : ℝ) ^ 2) b ∧
      Ydat n f rd (g * (n : ℝ) ^ 4 * (f : ℝ) ^ 2) b ≤ Ydat n f rd g b ^ 7 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hY0 : 0 ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    positivity
  have hnY : (n : ℝ) ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    calc (n : ℝ) = (n : ℝ) * 1 * 1 * 1 * 1 := by ring
      _ ≤ (n : ℝ) * f * rd * g * b := by gcongr
  have hfY : (f : ℝ) ≤ Ydat n f rd g b := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    calc (f : ℝ) = 1 * (f : ℝ) * 1 * 1 * 1 := by ring
      _ ≤ (n : ℝ) * f * rd * g * b := by gcongr
  have he : Ydat n f rd (g * (n : ℝ) ^ 4 * (f : ℝ) ^ 2) b = Ydat n f rd g b * ((n : ℝ) ^ 4 * (f : ℝ) ^ 2) := by
    unfold Formalism.HermitianLatticeCounting.S7.Ydat
    ring
  rw [he]
  constructor
  · have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 * (f : ℝ) ^ 2 := by
      have a1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hnR
      have a2 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := one_le_pow₀ hfR
      nlinarith
    nlinarith
  · calc Ydat n f rd g b * ((n : ℝ) ^ 4 * (f : ℝ) ^ 2)
        ≤ Ydat n f rd g b * (Ydat n f rd g b ^ 4 * Ydat n f rd g b ^ 2) := by gcongr
      _ = Ydat n f rd g b ^ 7 := by ring

theorem cnd_deepP (C Cq : ℝ) (hC : 1 ≤ C) (hCq : 0 ≤ Cq) (hCC : 16 * Cq ≤ C) :
    ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ C₁ ≥ C₁₀, ∀ (X : CData) (S : CSize X) (volK : ℝ)
    (n₀ : ℕ) (A : ℝ), 1 ≤ n₀ → X.HypB n₀ A → 1 ≤ X.qq → X.FinVol → S.Strata → S.DeepStepsQ volK C Cq →
    ∀ A₁ : ℝ, 1 ≤ A₁ → X.DeepInt A₁ (S.Mod C₁) := by
  obtain ⟨C₀, h1, hpt⟩ := cnd_pointG (4 * C) (by linarith)
  refine ⟨7 * C₀, by linarith, fun C₁ hC₁ X S volK n₀ A hn₀ hX hq hV hst hS A₁ hA₁ => ?_⟩
  obtain ⟨hvK, hvol, hae⟩ := hS
  have hY := cnd_two_le_Y X hn₀ hX
  have hn : 1 ≤ X.I.n := le_trans hn₀ hX.1.1
  have hnR : (1 : ℝ) ≤ (X.I.n : ℝ) := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ (X.I.f : ℝ) := by exact_mod_cast one_le_autInst_f X.I
  have hg1 : (1 : ℝ) ≤ (X.g : ℝ) := by exact_mod_cast hX.1.2.2.2.2.2.2.2.1
  have hb : 2 ≤ X.b := hX.1.2.2.1
  have hq2 := (X.qq_spec hX).2
  have hqR : (0 : ℝ) ≤ (X.qq : ℝ) := Nat.cast_nonneg _
  set g' : ℝ := (X.g : ℝ) * (X.I.n : ℝ) ^ 4 * (X.I.f : ℝ) ^ 2 with hg'
  have hg'1 : 1 ≤ g' := by
    have a1 : (1 : ℝ) ≤ (X.I.n : ℝ) ^ 4 := one_le_pow₀ hnR
    have a2 : (1 : ℝ) ≤ (X.I.f : ℝ) ^ 2 := one_le_pow₀ hfR
    have a3 : (1 : ℝ) ≤ (X.g : ℝ) * (X.I.n : ℝ) ^ 4 := by nlinarith
    rw [hg']
    nlinarith
  obtain ⟨hY1, hY7⟩ := cnd_Y' X.I.n X.I.f X.I.rd (X.g : ℝ) X.b hn (one_le_autInst_f X.I) (one_le_discriminant_root X.I) hg1 hb
  have hYY : cn_Y X = Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b := rfl
  rw [← hYY] at hY1 hY7
  have hYpos : 0 < cn_Y X := by linarith
  have hY'pos : 0 < Ydat X.I.n X.I.f X.I.rd g' X.b := lt_of_lt_of_le hYpos hY1
  have hτle : cn_tauS X C₁ ≤ Ydat X.I.n X.I.f X.I.rd g' X.b ^ (-(C₀ * (X.qq : ℝ))) := by
    have hnp : -(C₀ * (X.qq : ℝ)) ≤ 0 := by
      have : 0 ≤ C₀ * (X.qq : ℝ) := mul_nonneg (by linarith) hqR
      linarith
    have e1 : (cn_Y X ^ 7) ^ (-(C₀ * (X.qq : ℝ))) ≤ Ydat X.I.n X.I.f X.I.rd g' X.b ^ (-(C₀ * (X.qq : ℝ))) :=
      Real.rpow_le_rpow_of_nonpos hY'pos hY7 hnp
    have e2 : (cn_Y X ^ 7) ^ (-(C₀ * (X.qq : ℝ))) = cn_Y X ^ (-(7 * C₀ * (X.qq : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hYpos.le]
      congr 1
      push_cast
      ring
    have e3 : cn_tauS X C₁ ≤ cn_Y X ^ (-(7 * C₀ * (X.qq : ℝ))) := cnd_tauS_anti X hC₁ hY
    rw [e2] at e1
    exact le_trans e3 e1
  have hvol4 : X.I.vol X.μf X.fund / volK ≤
      Ydat X.I.n X.I.f X.I.rd g' X.b ^ (4 * C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) := by
    have hex : 0 ≤ C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) := by positivity
    refine le_trans hvol (le_trans (Real.rpow_le_rpow hYpos.le hY1 hex) ?_)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  refine cnd_deep_int X hV (S.measurableSet_Mod hst C₁) ?_ hA₁
  filter_upwards [hae] with x hx hxM
  have hlt : S.tau1 x < cn_tauS X C₁ := not_le.1 hxM
  have hhalf := lt_of_lt_of_le hlt (cnd_tauS_le_half X (by linarith : (1 : ℝ) ≤ C₁) hq hY)
  obtain ⟨a, τ, ha, haq, hpos, htop, hτ1, H⟩ := hx hhalf
  have hrd0 : 0 ≤ X.I.rd := le_trans zero_le_one (one_le_discriminant_root X.I)
  obtain ⟨ρ, Bs, r0, r1, r2, r3⟩ := cnd_refine C hC X.I.n X.qq X.I.f hq (one_le_autInst_f X.I) X.I.rd g' X.b (S.tau1 x)
    X.Dc volK |(X.kerD x).re| (one_le_discriminant_root X.I) hg'1 (hst.2.2.2.2.2.1 x).1 hhalf (Nat.cast_nonneg _) hvK a τ ha haq hpos
    htop hτ1 (fun b' hb1 hb2 => by
      obtain ⟨ρ, s, mult, s0, s1, s2, s3, s4, s5, s6⟩ := H b' hb1 hb2
      refine ⟨ρ, s, mult, s0, ?_, s2, s3, s4, s5, s6⟩
      have hρ₀ : 0 < τ b' / τ (b' + 1) := div_pos (hpos _) (hpos _)
      refine le_trans (cnd_diam_of_proved X Cq ρ _ hCq hρ₀ s1) ?_
      have : 0 ≤ (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * g' * X.I.rd * (τ b' / τ (b' + 1)) := by positivity
      nlinarith)
  exact hpt X.I.n X.qq X.I.f X.I.rd g' X.b (S.tau1 x) (cn_tauS X C₁) ρ _ Bs X.Dc _ volK hn hq hq2 (one_le_autInst_f X.I)
    (one_le_discriminant_root X.I) hg'1 hb (hst.2.2.2.2.2.1 x).1 hlt hτle (Nat.cast_nonneg _) hvK ENNReal.toReal_nonneg r0 r1 r2 r3 hvol4

end Formalism.MainNotions.LeviCoordinates

end
