import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnOneLtRd
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndRefine

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cn_two_pow (q : ℕ) : (2 : ℝ≥0∞) ^ q = ENNReal.ofReal ((2 : ℝ) ^ q) := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  simp

theorem cn_two_pow_mul (q : ℕ) {B : ℝ} : (2 : ℝ≥0∞) ^ q * ENNReal.ofReal (B / 2 ^ q) = ENNReal.ofReal B := by
  rw [cn_two_pow, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem cn_two_qq (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hn : 5 ≤ X.I.n) : 2 * X.qq + 1 ≤ X.I.n := by
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  by_cases h : X.qq ≤ 2
  · omega
  · nlinarith

theorem cn_prob : ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ Cv Cres : ℝ, 1 ≤ Cv → ∃ n₁ : ℕ, ∀ (X : CData) (S : CSize X) (n₀ : ℕ) (A C₁ : ℝ),
    n₁ ≤ X.I.n → X.HypB n₀ A → cn_tauS X C₁ ≤ 1 / 2 → X.FinVol → S.Strata → S.Density → S.KappaVol Cv →
    cn_ResBound X Cres → X.ProbMod c₂ (S.Mod C₁) := by
  obtain ⟨c₂, hc₂, n₂, hP⟩ := Formalism.HermitianLatticeCounting.Final.S7.probINonzero (1 / 8) (by norm_num)
  refine ⟨c₂, hc₂, fun Cv Cres hCv => ?_⟩
  obtain ⟨n₁, hκ⟩ := cn_kappa_le Cv Cres hCv
  refine ⟨max (max n₁ n₂) 5, fun X S n₀ A C₁ hn hX hts hV hS hD hK hR => ?_⟩
  have hn1 : n₁ ≤ X.I.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n₂ ≤ X.I.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn5 : 5 ≤ X.I.n := le_trans (le_max_right _ _) hn
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  set E : ℝ := Real.exp (-(c₂ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) with hE
  set vol : ℝ := X.I.vol X.μf X.fund with hvol
  have hvol0 : 0 ≤ vol := ENNReal.toReal_nonneg
  have hle : X.μ (S.Mod C₁)ᶜ ≤ ENNReal.ofReal (vol * E) := by
    refine le_trans (S.compl_Mod_le hS hD hts (cn_two_qq X hX hn5)) ?_
    refine le_trans (cn_sum_types_le X.qq _ (ENNReal.ofReal (vol * E / 2 ^ X.qq)) fun J hJ c => ?_) (cn_two_pow_mul _).le
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
    refine ENNReal.ofReal_le_ofReal ?_
    have a1 := hκ X S n₀ A hn1 hX hK hR J c h1 h2
    have a2 := hP X.I.n X.qq J X.I.f hn2 hq2 h1 (one_le_autInst_f X.I)
    have a3 : S.kap J c ≤ E / 2 ^ X.qq := by
      rw [le_div_iff₀ (by positivity)]
      calc S.kap J c * 2 ^ X.qq ≤ Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) * 2 ^ X.qq := by
            gcongr
        _ = 2 ^ X.qq * Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) := mul_comm _ _
        _ ≤ E := a2
    calc vol * S.kap J c ≤ vol * (E / 2 ^ X.qq) := mul_le_mul_of_nonneg_left a3 hvol0
      _ = vol * E / 2 ^ X.qq := by ring
  have : IsFiniteMeasure X.μ := ⟨by
    unfold CData.μ
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hV⟩
  have hadd := measureReal_add_measureReal_compl (μ := X.μ) (S.measurableSet_Mod hS C₁)
  have hc : X.μ.real (S.Mod C₁)ᶜ ≤ vol * E :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hvol0 (Real.exp_pos _).le) hle
  unfold CData.ProbMod
  rw [← hE, ← hvol]
  have hv : vol = X.μ.real Set.univ := X.vol_eq
  nlinarith

theorem cn_near : ∃ cb c₂ : ℝ, 0 < cb ∧ 0 < c₂ ∧ ∀ Cv Cres A C₁ : ℝ, 1 ≤ Cv → 1 ≤ A → 1 ≤ C₁ → ∃ n₁ : ℕ,
    ∀ (X : CData) (S : CSize X) (n₀ : ℕ) (C cε : ℝ), n₁ ≤ X.I.n → 1 ≤ n₀ → X.HypC n₀ A C cb → 1 ≤ X.qq → 0 < cε →
    cε ≤ 1 / 90000 → S.Strata → S.Density → S.KappaVol Cv → cn_ResBound X Cres →
    S.NearCount (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) (3 * Real.sqrt ((X.I.n : ℝ) * Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f)) →
    X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₂ 1 (S.Mod C₁) := by
  obtain ⟨cb, c₂, hcb, hc₂, hT⟩ := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.nearTotalAbs (1 / 8) (by norm_num)
  refine ⟨cb, c₂, hcb, hc₂, fun Cv Cres A C₁ hCv hA hC₁ => ?_⟩
  obtain ⟨n₁, hκ⟩ := cn_kappa_le Cv Cres hCv
  obtain ⟨n₂, hT⟩ := hT (2 * C₁) A (by linarith) hA
  refine ⟨max (max n₁ n₂) 5, fun X S n₀ C cε hn hn₀ hXC hq1 hcε hcε2 hS hD hK hR hN => ?_⟩
  have hX := hXC.1
  have hn1 : n₁ ≤ X.I.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n₂ ≤ X.I.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn5 : 5 ≤ X.I.n := le_trans (le_max_right _ _) hn
  obtain ⟨-, hq2⟩ := X.qq_spec hX
  have hY : 2 ≤ cn_Y X := cnd_two_le_Y X hn₀ hX
  have hf := one_le_autInst_f X.I
  obtain ⟨d1, -, -, -⟩ := Formalism.HermitianLatticeCounting.Final.S7.deltaSmall X.I.n X.qq X.I.f cε (by omega) hf hq2 hcε hcε2
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set M : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hM
  have hM0 : 0 ≤ M := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  set E : ℝ := Real.exp (-(c₂ * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) with hE
  set vol : ℝ := X.I.vol X.μf X.fund with hvol
  have hvol0 : 0 ≤ vol := ENNReal.toReal_nonneg
  have hts0 : 0 < cn_tauS X C₁ := cnd_tauS_pos X C₁ hY
  have hts : cn_tauS X C₁ ≤ 1 / 2 := cnd_tauS_le_half X hC₁ hq1 hY
  have hmain := S.near_le hS hD hN hX hts0 hts (cn_two_qq X hX hn5) (by positivity) d1
  unfold CData.NearStep
  refine le_trans hmain ?_
  have hDs : 1 * E * X.Ds = M * vol * E := by
    unfold CData.Ds AutInst.Dstar
    rw [hM, hvol]
    ring
  rw [← hE, hDs]
  refine le_trans (cn_sum_types_le X.qq _ (ENNReal.ofReal (M * vol * E / 2 ^ X.qq)) fun J hJ c => ?_) (cn_two_pow_mul _).le
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
  have a1 := hκ X S n₀ A hn1 hX hK hR J c h1 h2
  have hjq : ∀ x, c.blocksFun x ≤ X.qq := fun x => by
    have : c.blocksFun x ≤ ∑ y, c.blocksFun y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    rw [c.sum_blocksFun] at this
    exact le_trans this h2
  obtain ⟨-, -, a2⟩ := Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.logVolumeBound c.length X.qq X.I.f c.blocksFun C₁ (cn_Y X) hC₁ hY hq1 hjq
  have hg1 : (1 : ℝ) ≤ (X.g : ℝ) := by exact_mod_cast hX.1.2.2.2.2.2.2.2.1
  have a3 := hT X.I.n X.qq J c.length X.I.f X.I.rd X.g X.b hn2 hq2 (c.length_pos_of_pos h1) c.length_le h2 hf hXC.2.2.1
    hX.1.2.2.1 hg1 hX.1.2.2.2.2.2.2.2.2.1 (one_le_discriminant_root X.I) hX.1.2.2.2.1 hXC.2.2.2
  set k' : ℝ := Real.exp (-(1 / 8 * (J : ℝ) * (X.I.n : ℝ) * (X.I.f : ℝ) * Real.log (X.I.n : ℝ))) with hk'
  set P : ℝ := ∏ a, (2 * (X.I.f : ℝ) * c.blocksFun a * Real.log (1 / (2 * cn_tauS X C₁))) with hP
  set P' : ℝ := (2 * C₁ * (X.I.f : ℝ) * (X.qq : ℝ) ^ 2 * Real.log (cn_Y X)) ^ c.length with hP'
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun a _ => by
    have : 0 ≤ Real.log (1 / (2 * cn_tauS X C₁)) := Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity)]; linarith)
    positivity
  have hPP : P ≤ P' := a2
  have hk0 : 0 ≤ k' := (Real.exp_pos _).le
  calc ENNReal.ofReal M * (ENNReal.ofReal (vol * S.kap J c) * (2 * ENNReal.ofReal P))
      ≤ ENNReal.ofReal M * (ENNReal.ofReal (vol * k') * (ENNReal.ofReal 2 * ENNReal.ofReal P')) := by
        have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [← e2]
        gcongr
    _ = ENNReal.ofReal (M * (vol * k' * (2 * P'))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hM0]
    _ ≤ ENNReal.ofReal (M * vol * E / 2 ^ X.qq) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have a4 : k' * (2 * P') ≤ E / 2 ^ X.qq := by
          rw [le_div_iff₀ (by positivity)]
          calc k' * (2 * P') * 2 ^ X.qq = 2 ^ X.qq * (2 * k') * P' := by ring
            _ ≤ E := a3
        calc M * (vol * k' * (2 * P')) = M * vol * (k' * (2 * P')) := by ring
          _ ≤ M * vol * (E / 2 ^ X.qq) := mul_le_mul_of_nonneg_left a4 (by positivity)
          _ = _ := by ring

end Formalism.MainNotions.LeviCoordinates

end
