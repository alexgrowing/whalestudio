import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantMomentBoundBothSidesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureEqNormalFormRootMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSidesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHypsStatement

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRange

theorem one_le_foldr_max (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons a L ih => exact le_trans ih (le_max_right _ _)

theorem le_foldr_max (L : List ℝ) (x : ℝ) (hx : x ∈ L) : x ≤ L.foldr max 1 := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem ratio_le (r k N e : ℕ) (b v g θ θ' ka X Cg : ℝ) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) (hg : 1 ≤ g)
    (hgb : g ≤ b ^ (2 * Cg)) (hka : ka = Real.pi / v) (hθ0 : 0 < θ) (hθ : θ ≤ b ^ X) (hθ' : b ^ (-X) ≤ θ')
    (hN : N ≤ r ^ 2) (he : e ≤ r * k) :
    (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N) ≤
      b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) * v⁻¹ ^ e := by
  have hb0 : 0 < b := by linarith
  have hv0 : 0 < v := by linarith
  have hg0 : 0 < g := by linarith
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'
  have hpi := Real.pi_pos
  have e1 : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  have e2 : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast]; push_cast; rfl
  have e3 : 2 * ka / g / (2 * Real.pi) = (v * g)⁻¹ := by
    rw [hka]; field_simp
  have e4 : (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N)
      = (θ * θ'⁻¹ * (2 ^ (r ^ 2) * (v * g) ^ N)) * v⁻¹ ^ (r * k) := by
    rw [e1, e2, e3, pow_add, mul_pow 2 v, inv_pow, inv_pow]
    field_simp
  rw [e4]
  have h1 : θ'⁻¹ ≤ b ^ X := by
    have := inv_anti₀ (Real.rpow_pos_of_pos hb0 _) hθ'
    rwa [Real.rpow_neg hb0.le, inv_inv] at this
  have h2 : (v * g) ^ N ≤ (b * b ^ (2 * Cg)) ^ (r ^ 2) := by
    refine le_trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hv hg) hN) ?_
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul (by linarith) hgb hg0.le hb0.le) _
  have h3 : (2 : ℝ) ^ (r ^ 2) ≤ b ^ (r ^ 2) := pow_le_pow_left₀ (by norm_num) hb _
  have h4 : v⁻¹ ^ (r * k) ≤ v⁻¹ ^ e := pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hv) he
  have e5 : b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) =
      b ^ X * b ^ X * (b ^ (r ^ 2) * (b * b ^ (2 * Cg)) ^ (r ^ 2)) := by
    rw [← mul_pow, ← mul_assoc, ← Real.rpow_add hb0, Real.rpow_add hb0 (2 * X), Real.rpow_mul hb0.le (2 + 2 * Cg),
      Real.rpow_add hb0 2, Real.rpow_two, two_mul X, sq b, ← Real.rpow_natCast _ (r ^ 2)]
    push_cast; rfl
  rw [e5]
  gcongr

theorem absBd_le (r k : ℕ) (b v Q A De Dd C M m : ℝ) (hr : 1 ≤ r) (hm : m = 2 * r + 2) (hb : Real.exp 1 ≤ b)
    (hv : 0 < v) (hM : 0 ≤ M) (hDe : 1 ≤ De) (hD : 0 ≤ Dd)
    (hQ : Q ≤ b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r)))
    (hC : A + 44 + 24 * M ≤ C) (hC1 : 14 ≤ C) (hC2 : 8 * Real.pi * Real.exp 1 ≤ C) :
    Q * absBd k r (b ^ (M * m)) De Dd ≤
      (b ^ (C * m) * De) ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hb
  have hb0 : 0 < b := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm0 : 0 ≤ m := by linarith
  have hpi := Real.pi_pos
  have h1 : (4 * r : ℝ) ≤ b ^ m := by
    have a1 : Real.exp m ≤ b ^ m := by
      rw [← Real.exp_one_rpow]; exact Real.rpow_le_rpow (Real.exp_pos 1).le hb hm0
    have a2 : (r : ℝ) + 1 + 1 ≤ Real.exp (r + 1) := Real.add_one_le_exp _
    have a3 : Real.exp m = Real.exp (r + 1) * Real.exp (r + 1) := by rw [← Real.exp_add, hm]; ring_nf
    nlinarith
  have h2 : (4 * r : ℝ) ^ (44 * r ^ 3) ≤ b ^ (44 * (m * (r : ℝ) ^ 3)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) h1 _) (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h3 : (b ^ (M * m)) ^ (24 * r ^ 3) = b ^ (24 * M * (m * (r : ℝ) ^ 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h4 : De ^ (14 * r ^ 2) ≤ De ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hDe ?_
    push_cast
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
    exact mul_le_mul hC1 this (by positivity) (by linarith)
  have h5 : (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) ≤ (C / k) ^ (r * (k - 2 - r)) := by
    gcongr
  have h6 : b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) ≤
      (b ^ (C * m)) ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_mul hb0.le]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have t : 0 ≤ m * (r : ℝ) ^ 3 := by positivity
    have c : A + 44 + 24 * M ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right c t
    nlinarith
  have hC0 : 0 ≤ C := by linarith
  calc Q * absBd k r (b ^ (M * m)) De Dd
      ≤ (b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r))) *
        (b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) * De ^ (C * (r : ℝ) ^ 3) *
          (C / k) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹) := by
        unfold absBd
        rw [h3]
        refine mul_le_mul hQ ?_ (by positivity) (by positivity)
        gcongr
    _ = (b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3))) *
          De ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
        rw [show C / (k * v) = C / k * v⁻¹ by rw [← div_div, div_eq_mul_inv], mul_pow]; ring
    _ ≤ _ := by
        rw [Real.mul_rpow (by positivity) (by linarith)]
        gcongr

theorem abs_range : ∀ Cg cb Cu cT CT C0 C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C0 C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.majorantMomentBound_both_sides D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dif_pos (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := GlobalTheory.T.cellPoint_blockEnds_leadingMinors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dif_pos l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRange
