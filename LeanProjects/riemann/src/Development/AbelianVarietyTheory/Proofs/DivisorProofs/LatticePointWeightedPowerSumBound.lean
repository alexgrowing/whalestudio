import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumPiProdEnnreal
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

open scoped ENNReal

namespace GlobalTheory

theorem tsum_rpow_prod_add_le_of_box_count : ∀ (ι : Type) [Fintype ι] (s : ℝ), 1 < s → ∃ C : ℝ, ∀ (S : Type) (f : S → ι → ℝ) (K : ℝ) (A : ι → ℝ),
    (∀ c w, 0 ≤ f c w) → 0 ≤ K → (∀ w, 0 < A w) →
    (∀ T : ι → ℝ, (∀ w, 0 ≤ T w) → {c | ∀ w, f c w ≤ T w}.Finite ∧
      ({c | ∀ w, f c w ≤ T w}.ncard : ℝ) ≤ 1 + K * ∏ w, T w) →
    ∑' c : S, ENNReal.ofReal ((∏ w, (A w + f c w)) ^ (-s)) ≤
      ENNReal.ofReal (C * (1 + K * ∏ w, A w) * (∏ w, A w) ^ (-s)) := by
  intro ι _ s hs
  set n := Fintype.card ι
  set q1 : ℝ := (2:ℝ) ^ (-s) with hq1def
  set q2 : ℝ := 2 * q1 with hq2def
  have hq1 : 0 ≤ q1 := by positivity
  have hq2 : 0 ≤ q2 := by positivity
  have hq1lt : q1 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq2lt : q2 < 1 := by
    have : q2 = (2:ℝ) ^ (1 + -s) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    rw [this]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set G1 : ℝ := (1 - q1)⁻¹
  set G2 : ℝ := (1 - q2)⁻¹
  have hG1 : 0 ≤ G1 := inv_nonneg.2 (by linarith)
  have hG2 : 0 ≤ G2 := inv_nonneg.2 (by linarith)
  refine ⟨2 ^ n * (G1 ^ n + G2 ^ n), ?_⟩
  intro S f K A hf hK hA hbox
  set P : ℝ := ∏ w, A w with hPdef
  have hP : 0 < P := Finset.prod_pos fun w _ => hA w
  set x : S → ι → ℝ := fun c w => f c w / A w with hxdef
  have hx0 : ∀ c w, 0 ≤ x c w := fun c w => div_nonneg (hf c w) (hA w).le
  set mc : S → ι → ℕ := fun c w => Nat.log 2 ⌊x c w⌋₊ with hmcdef
  have hlow : ∀ c w, (2:ℝ) ^ (mc c w) ≤ 1 + x c w := by
    intro c w
    by_cases h : ⌊x c w⌋₊ = 0
    · simp only [hmcdef, h, Nat.log_zero_right, pow_zero]; linarith [hx0 c w]
    · have h1 : 2 ^ (mc c w) ≤ ⌊x c w⌋₊ := Nat.pow_log_le_self 2 h
      have h2 : ((2 ^ (mc c w) : ℕ) : ℝ) ≤ (⌊x c w⌋₊ : ℝ) := by exact_mod_cast h1
      have h3 := Nat.floor_le (hx0 c w)
      push_cast at h2; linarith
  have hup : ∀ c w, x c w ≤ 2 * 2 ^ (mc c w) := by
    intro c w
    have h1 : ⌊x c w⌋₊ < 2 ^ (mc c w).succ := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : ((⌊x c w⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (mc c w).succ : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 := Nat.lt_floor_add_one (x c w)
    push_cast at h2; rw [pow_succ] at h2; linarith

  set b : (ι → ℕ) → ℝ := fun m => P ^ (-s) * ∏ w, q1 ^ (m w) with hbdef
  have hterm : ∀ c, ENNReal.ofReal ((∏ w, (A w + f c w)) ^ (-s)) ≤ ENNReal.ofReal (b (mc c)) := by
    intro c
    apply ENNReal.ofReal_le_ofReal
    have hle : ∏ w, (A w * 2 ^ (mc c w)) ≤ ∏ w, (A w + f c w) := by
      apply Finset.prod_le_prod (fun w _ => by have := hA w; positivity)
      intro w _
      have : A w + f c w = A w * (1 + x c w) := by
        simp only [hxdef]; field_simp [(hA w).ne']
      rw [this]; exact mul_le_mul_of_nonneg_left (hlow c w) (hA w).le
    have hpos : 0 < ∏ w, (A w * 2 ^ (mc c w)) := Finset.prod_pos fun w _ => by have := hA w; positivity
    refine (Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Real.mul_rpow hP.le (by positivity)]
    simp only [hbdef]
    congr 1
    rw [← Real.finset_prod_rpow _ _ (fun w _ => by positivity)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hq1def, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]

  have hsplit : ∑' c, ENNReal.ofReal (b (mc c)) =
      ∑' m : ι → ℕ, ({c | mc c = m} : Set S).encard * ENNReal.ofReal (b m) := by
    calc ∑' c, ENNReal.ofReal (b (mc c))
        = ∑' c, ∑' m : ι → ℕ, (if mc c = m then ENNReal.ofReal (b m) else 0) := by
          refine tsum_congr fun c => ?_
          rw [tsum_eq_single (mc c) (fun m hm => by simp [Ne.symm hm])]
          simp
      _ = ∑' m : ι → ℕ, ∑' c, (if mc c = m then ENNReal.ofReal (b m) else 0) := ENNReal.tsum_comm
      _ = _ := by
          refine tsum_congr fun m => ?_
          rw [← ENNReal.tsum_set_const, tsum_subtype {c | mc c = m} (fun _ => ENNReal.ofReal (b m))]
          refine tsum_congr fun c => ?_
          simp [Set.indicator_apply]
  set T : (ι → ℕ) → ι → ℝ := fun m w => A w * (2 * 2 ^ (m w)) with hTdef
  have hcount : ∀ m : ι → ℕ, ({c | mc c = m} : Set S).encard ≤
      ENNReal.ofReal (1 + K * ∏ w, T m w) := by
    intro m
    have hT : ∀ w, 0 ≤ T m w := fun w => by have := hA w; positivity
    obtain ⟨hfin, hnc⟩ := hbox (T m) hT
    have hsub : ({c | mc c = m} : Set S) ⊆ {c | ∀ w, f c w ≤ T m w} := by
      intro c hc w
      simp only [Set.mem_setOf_eq] at hc
      have h1 := hup c w
      rw [hc] at h1
      have : f c w = A w * x c w := by simp only [hxdef]; field_simp [(hA w).ne']
      rw [this]; exact mul_le_mul_of_nonneg_left h1 (hA w).le
    calc (({c | mc c = m} : Set S).encard : ℝ≥0∞)
        ≤ (({c | ∀ w, f c w ≤ T m w} : Set S).encard : ℝ≥0∞) := by
          exact_mod_cast Set.encard_le_encard hsub
      _ = ((({c | ∀ w, f c w ≤ T m w} : Set S).ncard : ℕ) : ℝ≥0∞) := by
          rw [← hfin.cast_ncard_eq]; rfl
      _ = ENNReal.ofReal (({c | ∀ w, f c w ≤ T m w} : Set S).ncard : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hnc

  have hp1 : ∀ m : ι → ℕ, 0 ≤ ∏ w, q1 ^ m w := fun m => Finset.prod_nonneg fun w _ => pow_nonneg hq1 _
  have hp2 : ∀ m : ι → ℕ, 0 ≤ ∏ w, q2 ^ m w := fun m => Finset.prod_nonneg fun w _ => pow_nonneg hq2 _
  have hPs : 0 ≤ P ^ (-s) := Real.rpow_nonneg hP.le _
  have hKnP : 0 ≤ K * 2 ^ n * P := by positivity
  have hshell : ∀ m : ι → ℕ, ENNReal.ofReal (1 + K * ∏ w, T m w) * ENNReal.ofReal (b m) =
      ENNReal.ofReal (P ^ (-s)) * (∏ w, ENNReal.ofReal q1 ^ m w +
        ENNReal.ofReal (K * 2 ^ n * P) * ∏ w, ENNReal.ofReal q2 ^ m w) := by
    intro m
    have e1 : ∏ w, T m w = P * (2 ^ n * ∏ w, (2:ℝ) ^ m w) := by
      simp only [hTdef, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hPdef, n]
    have e2 : ∏ w, q2 ^ m w = (∏ w, (2:ℝ) ^ m w) * ∏ w, q1 ^ m w := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun w _ => by rw [hq2def, mul_pow]
    have hreal : (1 + K * ∏ w, T m w) * b m =
        P ^ (-s) * (∏ w, q1 ^ m w + K * 2 ^ n * P * ∏ w, q2 ^ m w) := by
      rw [e1, e2]; simp only [hbdef]; ring
    have hTn : 0 ≤ 1 + K * ∏ w, T m w := by
      rw [e1]; have := Finset.prod_nonneg fun w (_ : w ∈ Finset.univ) => pow_nonneg (zero_le_two (α := ℝ)) (m w)
      positivity
    rw [← ENNReal.ofReal_mul hTn, hreal, ENNReal.ofReal_mul hPs,
      ENNReal.ofReal_add (hp1 m) (mul_nonneg hKnP (hp2 m)), ENNReal.ofReal_mul hKnP,
      ENNReal.ofReal_prod_of_nonneg (fun w _ => pow_nonneg hq1 _),
      ENNReal.ofReal_prod_of_nonneg (fun w _ => pow_nonneg hq2 _)]
    simp only [ENNReal.ofReal_pow hq1, ENNReal.ofReal_pow hq2]
  have hgeo : ∀ q : ℝ, 0 ≤ q → q < 1 →
      ∑' m : ι → ℕ, ∏ w, ENNReal.ofReal q ^ m w = ENNReal.ofReal ((1 - q)⁻¹) ^ n := by
    intro q h0 h1
    rw [GlobalTheory.HL.tsum_pi_prod_ennreal (X := fun _ => ℕ) (fun _ j => ENNReal.ofReal q ^ j),
      Finset.prod_const, Finset.card_univ, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ h0, ENNReal.ofReal_inv_of_pos (by linarith)]
  have hfin : P ^ (-s) * (G1 ^ n + K * 2 ^ n * P * G2 ^ n) ≤
      2 ^ n * (G1 ^ n + G2 ^ n) * (1 + K * P) * P ^ (-s) := by
    have h2n : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hKP : 0 ≤ K * P := mul_nonneg hK hP.le
    have ha := pow_nonneg hG1 n
    have hb := pow_nonneg hG2 n
    have h2 : (0:ℝ) ≤ 2 ^ n := by positivity
    have key : G1 ^ n + K * 2 ^ n * P * G2 ^ n ≤ 2 ^ n * (G1 ^ n + G2 ^ n) * (1 + K * P) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2n) ha, mul_nonneg h2 hb,
        mul_nonneg (mul_nonneg hKP h2) ha, mul_nonneg (mul_nonneg hKP h2) hb]
    calc P ^ (-s) * (G1 ^ n + K * 2 ^ n * P * G2 ^ n)
        ≤ P ^ (-s) * (2 ^ n * (G1 ^ n + G2 ^ n) * (1 + K * P)) := mul_le_mul_of_nonneg_left key hPs
      _ = _ := by ring
  calc ∑' c, ENNReal.ofReal ((∏ w, (A w + f c w)) ^ (-s))
      ≤ ∑' c, ENNReal.ofReal (b (mc c)) := ENNReal.tsum_le_tsum hterm
    _ = ∑' m : ι → ℕ, ({c | mc c = m} : Set S).encard * ENNReal.ofReal (b m) := hsplit
    _ ≤ ∑' m : ι → ℕ, ENNReal.ofReal (1 + K * ∏ w, T m w) * ENNReal.ofReal (b m) :=
        ENNReal.tsum_le_tsum fun m => by gcongr; exact hcount m
    _ = ∑' m : ι → ℕ, ENNReal.ofReal (P ^ (-s)) * (∏ w, ENNReal.ofReal q1 ^ m w +
        ENNReal.ofReal (K * 2 ^ n * P) * ∏ w, ENNReal.ofReal q2 ^ m w) := tsum_congr hshell
    _ = ENNReal.ofReal (P ^ (-s)) * (ENNReal.ofReal G1 ^ n + ENNReal.ofReal (K * 2 ^ n * P) * ENNReal.ofReal G2 ^ n) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left, hgeo q1 hq1 hq1lt, hgeo q2 hq2 hq2lt]
    _ = ENNReal.ofReal (P ^ (-s) * (G1 ^ n + K * 2 ^ n * P * G2 ^ n)) := by
        rw [ENNReal.ofReal_mul hPs, ENNReal.ofReal_add (pow_nonneg hG1 n) (mul_nonneg hKnP (pow_nonneg hG2 n)),
          ENNReal.ofReal_mul hKnP, ENNReal.ofReal_pow hG1, ENNReal.ofReal_pow hG2]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

end GlobalTheory
