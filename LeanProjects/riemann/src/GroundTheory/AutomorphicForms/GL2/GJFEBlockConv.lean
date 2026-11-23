import Mathlib
import GroundTheory.AutomorphicForms.GL2.IsAddHaarMeasureMatrixMeasureFinSq

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open GLnLocal MeasureTheory Measure Polynomial ValuativeRel
open scoped NNReal ENNReal

theorem hasSum_geom_poly {β : ℂ} (hβ : β ≠ 0) (e : ℕ) {P : ℤ → ℂ[X]} {j₀ j₁ : ℤ} (hj : j₀ ≤ j₁)
    (h0 : ∀ j < j₀, P j = 0) (h1 : ∀ j ≥ j₁, P j = P j₁) :
    ∃ (Pn : ℂ[X]) (N : ℕ), ∀ x : ℂ, x ≠ 0 → ‖β * x ^ e‖ < 1 →
      HasSum (fun j : ℤ => (β * x ^ e) ^ j * (P j).eval x)
        (Pn.eval x / (x ^ N * (1 - β * x ^ e))) := by
  classical
  set N : ℕ := e * (-j₀).toNat with hN
  have hNj : ∀ j, j₀ ≤ j → (0 : ℤ) ≤ (N : ℤ) + e * j := by
    intro j hj'
    have : (-j₀ : ℤ) ≤ ((-j₀).toNat : ℤ) := Int.self_le_toNat _
    have he : (0 : ℤ) ≤ e := Int.natCast_nonneg e
    push_cast [hN]
    nlinarith
  set S : Finset ℤ := Finset.Ico j₀ j₁
  set Pn : ℂ[X] := (1 - C β * X ^ e) * ∑ j ∈ S, C (β ^ j) * X ^ ((N : ℤ) + e * j).toNat * P j +
    C (β ^ j₁) * X ^ ((N : ℤ) + e * j₁).toNat * P j₁ with hPn
  refine ⟨Pn, N, fun x hx hlt => ?_⟩
  have hne : (1 : ℂ) - β * x ^ e ≠ 0 := by
    intro h
    have : β * x ^ e = 1 := by linear_combination -h
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hxN : x ^ N ≠ 0 := pow_ne_zero _ hx

  have hpow : ∀ j, j₀ ≤ j → (β * x ^ e) ^ j * x ^ N = β ^ j * x ^ ((N : ℤ) + e * j).toNat := by
    intro j hj'
    rw [mul_zpow, ← zpow_natCast x ((N : ℤ) + e * j).toNat, Int.toNat_of_nonneg (hNj j hj'),
      zpow_add₀ hx, zpow_natCast, ← zpow_natCast x e, ← _root_.zpow_mul]
    ring

  set f : ℤ → ℂ := fun j => (β * x ^ e) ^ j * (P j).eval x
  have hfin : HasSum (fun j => if j < j₁ then f j else 0) (∑ j ∈ S, f j) := by
    have h : HasSum (fun j : ℤ => if j < j₁ then f j else 0)
        (∑ j ∈ S, (if j < j₁ then f j else 0)) := hasSum_sum_of_ne_finset_zero fun j hj => ?_
    · convert h using 1
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [S, Finset.mem_Ico] at hj
      simp [hj.2]
    · simp only [S, Finset.mem_Ico, not_and_or, not_le] at hj
      split_ifs with h
      · rcases hj with hj | hj
        · simp [f, h0 j hj]
        · exact absurd h hj
      · rfl
  have hz : β * x ^ e ≠ 0 := mul_ne_zero hβ (pow_ne_zero _ hx)
  have htail : HasSum (fun j => if j < j₁ then 0 else f j)
      ((β * x ^ e) ^ j₁ * (P j₁).eval x * (1 - β * x ^ e)⁻¹) := by
    have hg : HasSum (fun k : ℕ => (β * x ^ e) ^ j₁ * (P j₁).eval x * (β * x ^ e) ^ k)
        ((β * x ^ e) ^ j₁ * (P j₁).eval x * (1 - β * x ^ e)⁻¹) :=
      (hasSum_geometric_of_norm_lt_one hlt).mul_left _
    have hinj : Function.Injective (fun k : ℕ => j₁ + (k : ℤ)) := fun a b h => by
      simpa using h
    rw [← hinj.hasSum_iff fun j hj => ?_]
    · convert hg using 1
      funext k
      simp only [Function.comp_apply, f]
      rw [if_neg (by omega), h1 _ (by omega), zpow_add₀ hz, zpow_natCast]
      ring
    · split_ifs with h
      · rfl
      · exact absurd ⟨(j - j₁).toNat, by simp; omega⟩ hj
  have htot := hfin.add htail
  have hf : (fun j => (if j < j₁ then f j else 0) + (if j < j₁ then 0 else f j)) = f := by
    funext j; split_ifs <;> simp
  rw [hf] at htot
  convert htot using 1
  rw [div_eq_iff (mul_ne_zero hxN hne)]
  simp only [Pn, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_pow, eval_X, eval_finsetSum]
  have hS : ∀ j ∈ S, β ^ j * x ^ ((N : ℤ) + e * j).toNat * (P j).eval x =
      f j * x ^ N := fun j hj => by
    simp only [S, Finset.mem_Ico] at hj
    simp only [f]
    rw [← hpow j hj.1]
    ring
  rw [Finset.sum_congr rfl hS, ← Finset.sum_mul, ← hpow j₁ hj]
  field_simp

theorem tsum_int_lt_top_of_le_geom {a : ℤ → ℝ≥0∞} {j₀ : ℤ} {M r : ℝ≥0∞} (hM : M ≠ ∞) (hr : r < 1)
    (h0 : ∀ j < j₀, a j = 0) (h1 : ∀ k : ℕ, a (j₀ + k) ≤ M * r ^ k) : ∑' j, a j < ∞ := by
  have hinj : Function.Injective (fun k : ℕ => j₀ + (k : ℤ)) := fun x y h => by simpa using h
  have hsupp : Function.support a ⊆ Set.range (fun k : ℕ => j₀ + (k : ℤ)) := by
    intro j hj
    by_contra hj'
    apply hj
    refine h0 j ?_
    by_contra hlt
    exact hj' ⟨(j - j₀).toNat, by simp; omega⟩
  rw [← hinj.tsum_eq hsupp]
  calc ∑' k : ℕ, a (j₀ + k) ≤ ∑' k : ℕ, M * r ^ k := ENNReal.tsum_le_tsum h1
    _ = M * (1 - r)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ∞ := ENNReal.mul_lt_top hM.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr))

theorem tsum_int_lt_top_of_le_geom₂ {a : ℤ → ℝ≥0∞} {M r₁ r₂ : ℝ≥0∞} (hM : M ≠ ∞) (hr₁ : r₁ < 1)
    (hr₂ : r₂ < 1) (h₁ : ∀ k : ℕ, a k ≤ M * r₁ ^ k) (h₂ : ∀ k : ℕ, a (-(k + 1 : ℤ)) ≤ M * r₂ ^ k) :
    ∑' j, a j < ∞ := by
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · calc ∑' k : ℕ, a k ≤ ∑' k : ℕ, M * r₁ ^ k := ENNReal.tsum_le_tsum h₁
      _ = M * (1 - r₁)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ∞ := ENNReal.mul_lt_top hM.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr₁))
  · calc ∑' k : ℕ, a (-(k + 1 : ℤ)) ≤ ∑' k : ℕ, M * r₂ ^ k := ENNReal.tsum_le_tsum fun k => by
          have := h₂ k
          push_cast at this ⊢
          exact this
      _ = M * (1 - r₂)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ∞ := ENNReal.mul_lt_top hM.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr₂))

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

variable (m) in

structure IsCentralCoeff (α : ℂ) (c : GL (Fin m) F → ℂ) : Prop where
  continuous : Continuous c
  ne_zero : α ≠ 0
  mul_left : ∀ g, c (centralUnif F m * g) = α * c g
  support : ∃ C : Set (GL (Fin m) F), IsCompact C ∧
    ∀ g, c g ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C

namespace IsCentralCoeff

variable {α : ℂ} {c : GL (Fin m) F → ℂ}

theorem zpow_mul (hc : IsCentralCoeff m α c) (j : ℤ) (g : GL (Fin m) F) :
    c (centralUnif F m ^ j * g) = α ^ j * c g := by
  induction j using Int.induction_on generalizing g with
  | zero => simp
  | succ k ih =>
    rw [_root_.zpow_add_one, mul_assoc, ih, hc.mul_left, zpow_add_one₀ hc.ne_zero]
    ring
  | pred k ih =>
    have h := hc.mul_left ((centralUnif F m)⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    rw [_root_.zpow_sub_one, mul_assoc, ih, zpow_sub_one₀ hc.ne_zero, h]
    field_simp [hc.ne_zero]

theorem inv (hc : IsCentralCoeff m α c) : IsCentralCoeff m α⁻¹ (fun g => c g⁻¹) := by
  refine ⟨hc.continuous.comp continuous_inv, inv_ne_zero hc.ne_zero, fun g => ?_, ?_⟩
  · show c (centralUnif F m * g)⁻¹ = α⁻¹ * c g⁻¹
    have e := centralUnif_zpow_mul_comm (-1) g⁻¹
    have h2 := hc.zpow_mul (-1) g⁻¹
    rw [zpow_neg_one] at e h2
    rw [zpow_neg_one] at h2
    rw [mul_inv_rev, ← e, h2]
  · obtain ⟨C, hC, hCs⟩ := hc.support
    refine ⟨(fun g => g⁻¹) '' C, hC.image continuous_inv, fun g hg => ?_⟩
    obtain ⟨j, hj⟩ := hCs _ hg
    refine ⟨-j, ⟨_, hj, ?_⟩⟩
    show (centralUnif F m ^ j * g⁻¹)⁻¹ = _
    rw [mul_inv_rev, inv_inv, ← zpow_neg, ← centralUnif_zpow_mul_comm]

theorem exists_compact_tile [NeZero m] (hc : IsCentralCoeff m α c) :
    ∃ K : Set (GL (Fin m) F), IsCompact K ∧ ∀ g ∈ tile F m 0, c g ≠ 0 → g ∈ K := by
  classical
  obtain ⟨C, hC, hCs⟩ := hc.support
  have hm : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hcont : Continuous (ordDet : GL (Fin m) F → ℤ) := isLocallyConstant_ordDet_GL.continuous
  obtain ⟨d₁, hd₁⟩ := (hC.image hcont).bddAbove
  obtain ⟨d₀, hd₀⟩ := (hC.image hcont).bddBelow
  refine ⟨⋃ j ∈ Finset.Icc (-|d₀| - 1) |d₁|, (fun h => centralUnif F m ^ (-j) * h) '' C,
    (Finset.Icc (-|d₀| - 1) |d₁|).isCompact_biUnion fun j _ => hC.image (continuous_mul_left _),
    fun g hg hcg => ?_⟩
  obtain ⟨j, hj⟩ := hCs g hcg
  have h1 := hd₁ ⟨_, hj, rfl⟩
  have h0 := hd₀ ⟨_, hj, rfl⟩
  simp only [ordDet_centralUnif_zpow_mul] at h1 h0
  obtain ⟨hg0, hg1⟩ := hg
  simp only [zero_mul, zero_add] at hg0 hg1
  refine Set.mem_biUnion (x := j) ?_ ⟨_, hj, by
    show centralUnif F m ^ (-j) * (centralUnif F m ^ j * g) = g
    rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]⟩
  simp only [Finset.coe_Icc, Set.mem_Icc]
  constructor
  · by_contra hlt
    push Not at hlt
    have hj1 : j + 1 < 0 := by linarith [abs_nonneg d₀]
    have h2 : (j + 1) * (m : ℤ) ≤ j + 1 := by nlinarith
    have h3 : (j + 1) * (m : ℤ) = j * m + m := by ring
    linarith [neg_abs_le d₀]
  · by_contra hlt
    push Not at hlt
    have : j ≤ j * (m : ℤ) := by nlinarith [abs_nonneg d₁]
    nlinarith [le_abs_self d₁]

theorem exists_bound_tile [NeZero m] (hc : IsCentralCoeff m α c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ tile F m 0, ‖c g‖ ≤ B := by
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun g hg => ?_⟩
  by_cases h : c g = 0
  · rw [h, norm_zero]; exact le_max_right _ _
  · exact (hB g (hKc g hg h)).trans (le_max_left _ _)

end IsCentralCoeff

theorem coe_centralUnif_zpow (j : ℤ) :
    ((centralUnif F m ^ j : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((uniformizer F : F) ^ j) • (1 : Matrix (Fin m) (Fin m) F) := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  induction j using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [_root_.zpow_add_one, Units.val_mul, ih, coe_centralUnif, smul_mul_smul_comm, one_mul,
      ← zpow_add_one₀ hϖ]
  | pred k ih =>
    have hinv : (((centralUnif F m)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        ((uniformizer F : F)⁻¹) • (1 : Matrix (Fin m) (Fin m) F) := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [coe_centralUnif, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hϖ, one_smul]
    rw [_root_.zpow_sub_one, Units.val_mul, ih, hinv, smul_mul_smul_comm, one_mul,
      ← zpow_sub_one₀ hϖ]

theorem IsSchwartzBruhat.exists_ordDet_ge {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ A : ℕ, ∀ g : GL (Fin m) F, Φ (g : Matrix (Fin m) (Fin m) F) ≠ 0 →
      -((m : ℤ) * A) ≤ ordDet g := by
  obtain ⟨r, A, -, hsupp⟩ := hΦ.exists_invariant
  refine ⟨A, fun g hg => ?_⟩
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hent := hsupp _ hg
  have hmem : (((uniformizer F : F) ^ A) • (g : Matrix (Fin m) (Fin m) F)).det ∈ 𝒪[F] :=
    det_mem_integer fun i j => by simpa using hent i j
  have hne : (((uniformizer F : F) ^ A) • (g : Matrix (Fin m) (Fin m) F)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hϖ)) (det_ne_zero g)
  have h := ord_nonneg_of_mem_integer hmem hne
  rw [Matrix.det_smul, LocalField.ord_mul (pow_ne_zero _ (pow_ne_zero _ hϖ)) (det_ne_zero g),
    ← pow_mul, LocalField.ord_pow hϖ, LocalField.ord_uniformizer (irreducible_uniformizer F)] at h
  simp only [Fintype.card_fin] at h
  unfold ordDet
  push_cast at h
  nlinarith

theorem IsSchwartzBruhat.exists_bound {Φ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X, ‖Φ X‖ ≤ B := by
  obtain ⟨B, hB⟩ := hΦ.1.continuous.bounded_above_of_compact_support hΦ.2
  exact ⟨max B 0, le_max_right _ _, fun X => (hB X).trans (le_max_left _ _)⟩

section Integrals

variable [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] [NeZero m] {α : ℂ}
  {c : GL (Fin m) F → ℂ}

theorem norm_detPow_le_of_mem_tile {g : GL (Fin m) F} (hg : g ∈ tile F m 0) (s : ℂ) :
    ‖detPow g s‖ ≤ 1 + ‖qs F s‖ ^ m := by
  obtain ⟨h0, h1⟩ := hg
  simp only [zero_mul, zero_add] at h0 h1
  rw [detPow_eq_qs_zpow, norm_zpow, ← Int.toNat_of_nonneg h0, zpow_natCast]
  have hk : (ordDet g).toNat ≤ m := by omega
  by_cases ht : ‖qs F s‖ ≤ 1
  · have := pow_le_one₀ (norm_nonneg (qs F s)) ht (n := (ordDet g).toNat)
    have := pow_nonneg (norm_nonneg (qs F s)) m
    linarith
  · push Not at ht
    have := pow_le_pow_right₀ ht.le hk
    linarith

theorem IsCentralCoeff.lintegral_tile_lt_top (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] (s : ℂ) :
    ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ < ∞ := by
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB0, hB⟩ := hc.exists_bound_tile
  set b : ℝ≥0∞ := ENNReal.ofReal (B * (1 + ‖qs F s‖ ^ m))
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  calc ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ
      ≤ ∫⁻ g in tile F m 0, K.indicator (fun _ => b) g ∂μ := by
        refine setLIntegral_mono (measurable_const.indicator hKm) fun g hg => ?_
        by_cases hcg : c g = 0
        · simp [hcg]
        · rw [Set.indicator_of_mem (hKc g hg hcg), ← ofReal_norm, norm_mul]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul (hB g hg) (norm_detPow_le_of_mem_tile hg s)
            (norm_nonneg _) hB0)
    _ ≤ ∫⁻ g, K.indicator (fun _ => b) g ∂μ := setLIntegral_le_lintegral _ _
    _ = b * μ K := lintegral_indicator_const hKm b
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

theorem IsCentralCoeff.lintegral_zeta_lt_top (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1) :
    ∫⁻ g, ‖Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * c g‖ₑ ∂μ < ∞ := by
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  set ρ : ℝ := ‖α * qs F s ^ m‖ with hρdef
  have hρ0 : 0 < ρ := norm_pos_iff.2 (mul_ne_zero hc.ne_zero (pow_ne_zero _ (qs_ne_zero s)))
  set K₁ := ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ
  have hK₁ : K₁ ≠ ∞ := (hc.lintegral_tile_lt_top μ s).ne
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

  have hval : ∀ (j : ℤ) (g : GL (Fin m) F),
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        detPow (centralUnif F m ^ j * g) s * c (centralUnif F m ^ j * g) =
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        (α * qs F s ^ m) ^ j * (c g * detPow g s) := by
    intro j g
    rw [detPow_centralUnif_zpow_mul, IsCentralCoeff.zpow_mul hc, mul_zpow, mul_comm j,
      _root_.zpow_mul, zpow_natCast]
    ring
  rw [lintegral_eq_tsum_tile μ]
  refine tsum_int_lt_top_of_le_geom (j₀ := -(A : ℤ)) (r := ENNReal.ofReal ρ)
    (M := ENNReal.ofReal (BΦ * ρ ^ (-(A : ℤ))) * K₁) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK₁)
    (ENNReal.ofReal_lt_one.2 hs) (fun j hj => ?_) (fun k => ?_)
  · refine (setLIntegral_congr_fun (measurableSet_tile 0) fun g hg => ?_).trans (lintegral_zero)
    show ‖_‖ₑ = 0
    rw [enorm_eq_zero]
    by_contra hne
    have hΦne : Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) ≠ 0 := by
      intro h; apply hne; rw [h]; ring
    have h1 := hA _ hΦne
    rw [ordDet_centralUnif_zpow_mul] at h1
    obtain ⟨-, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg1
    have : (j + 1) * (m : ℤ) ≤ -(A : ℤ) * m := by nlinarith
    nlinarith
  · calc ∫⁻ g in tile F m 0, ‖Φ ((centralUnif F m ^ (-(A : ℤ) + k) * g : GL (Fin m) F) :
            Matrix (Fin m) (Fin m) F) * detPow (centralUnif F m ^ (-(A : ℤ) + k) * g) s *
            c (centralUnif F m ^ (-(A : ℤ) + k) * g)‖ₑ ∂μ
        ≤ ∫⁻ g in tile F m 0, (ENNReal.ofReal (BΦ * ρ ^ (-(A : ℤ))) * ENNReal.ofReal ρ ^ k) *
            ‖c g * detPow g s‖ₑ ∂μ := by
          refine lintegral_mono fun g => ?_
          rw [hval, enorm_mul, enorm_mul, ← ofReal_norm, ← ofReal_norm,
            norm_zpow, ← hρdef, zpow_add₀ hρ0.ne', zpow_natCast]
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_pow hρ0.le,
            ← ENNReal.ofReal_mul (mul_nonneg hBΦ0 (zpow_nonneg hρ0.le _))]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := hBΦ ((centralUnif F m ^ (-(A : ℤ) + k) * g : GL (Fin m) F) :
            Matrix (Fin m) (Fin m) F)
          have h2 : 0 ≤ ρ ^ (-(A : ℤ)) * ρ ^ k := mul_nonneg (zpow_nonneg hρ0.le _) (pow_nonneg hρ0.le _)
          nlinarith
      _ = _ := by rw [lintegral_const_mul' _ _ (by
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
                  ring

theorem IsCentralCoeff.integrable_zeta (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1) :
    Integrable (fun g : GL (Fin m) F => Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * c g) μ :=
  ⟨(((hΦ.1.continuous.comp Units.continuous_val).mul (continuous_detPow s)).mul
      hc.continuous).aestronglyMeasurable, hc.lintegral_zeta_lt_top μ hΦ hs⟩

theorem IsSchwartzBruhat.exists_eq_zero_of_small {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (B : ℕ) :
    ∃ J : ℤ, ∀ j ≥ J, ∀ g : GL (Fin m) F,
      (∀ i l, (g : Matrix (Fin m) (Fin m) F) i l ∈ LocalField.valBall F (-(B : ℤ))) →
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Φ 0 := by
  obtain ⟨r, A, hinv, -⟩ := hΦ.exists_invariant
  refine ⟨(r : ℤ) + B, fun j hj g hg => ?_⟩
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hϖO : (GLnLocal.uniformizer F : F) ∈ 𝒪[F] := (GLnLocal.uniformizer F).2
  set t : ℕ := (j - r - B).toNat with ht
  have hjt : j = (r : ℤ) + B + t := by omega
  have h := hinv 0 ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
    (fun i l => ?_)
  · rwa [zero_add] at h
  · refine ⟨(GLnLocal.uniformizer F : F) ^ t * ((GLnLocal.uniformizer F : F) ^ B * (g : Matrix (Fin m) (Fin m) F) i l),
      mul_mem (pow_mem hϖO t) (mem_valBall_neg_iff.1 (hg i l)), ?_⟩
    rw [Units.val_mul, coe_centralUnif_zpow, Matrix.smul_mul, one_mul, Matrix.smul_apply,
      smul_eq_mul, hjt, zpow_add₀ hϖ, zpow_add₀ hϖ, zpow_natCast, zpow_natCast, zpow_natCast]
    ring

theorem IsCentralCoeff.exists_eq_div_zeta (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ (Pn : ℂ[X]) (N : ℕ), ∀ s : ℂ, ‖α * qs F s ^ m‖ < 1 →
      ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * c g ∂μ =
        Pn.eval (qs F s) / (qs F s ^ N * (1 - α * qs F s ^ m)) := by
  classical
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := exists_valBall_of_isCompact (hK.image Units.continuous_val)
  obtain ⟨J, hJ⟩ := hΦ.exists_eq_zero_of_small B
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set J₁ : ℤ := max J (-(A : ℤ))

  set a : ℤ → ℕ → ℂ := fun j k => ∫ g in tile F m 0,
    (if ordDet g = k then Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      c g else 0) ∂μ with hadef
  set P : ℤ → ℂ[X] := fun j => ∑ k ∈ Finset.range m, C (a j k) * X ^ k with hPdef

  have hzero : ∀ j < -(A : ℤ), ∀ g ∈ tile F m 0,
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 0 := by
    intro j hj g hg
    by_contra hne
    have h1 := hA _ hne
    rw [ordDet_centralUnif_zpow_mul] at h1
    obtain ⟨-, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg1
    have : (j + 1) * (m : ℤ) ≤ -(A : ℤ) * m := by nlinarith
    nlinarith
  have h0 : ∀ j < -(A : ℤ), P j = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun k _ => ?_
    have : a j k = 0 := by
      refine (setIntegral_congr_fun (measurableSet_tile 0) fun g hg => ?_).trans (integral_zero _ _)
      show (if ordDet g = (k : ℤ) then _ else 0) = 0
      rw [hzero j hj g hg]
      simp
    rw [this, map_zero, zero_mul]

  have h1 : ∀ j ≥ J₁, P j = P J₁ := by
    intro j hj
    have hcoef : ∀ k, a j k = a J₁ k := fun k => by
      refine setIntegral_congr_fun (measurableSet_tile 0) fun g hg => ?_
      by_cases hcg : c g = 0
      · simp [hcg]
      have hgK := hKc g hg hcg
      have hent := hB _ ⟨g, hgK, rfl⟩
      rw [hJ j (le_trans (le_max_left _ _) hj) g hent,
        hJ J₁ (le_max_left _ _) g hent]
    simp only [hPdef, hcoef]
  obtain ⟨Pn, N, hsum⟩ := hasSum_geom_poly hc.ne_zero m (le_max_right J (-(A : ℤ))) h0 h1
  refine ⟨Pn, N, fun s hs => ?_⟩
  have hint := hc.integrable_zeta μ hΦ hs
  have h := hasSum_integral_tile μ hint
  refine h.unique ?_
  convert hsum (qs F s) (qs_ne_zero s) hs using 1
  funext j
  set x := qs F s with hx

  have hcint : IntegrableOn (fun g => ‖c g‖) (tile F m 0) μ := by
    refine ⟨hc.continuous.norm.aestronglyMeasurable, ?_⟩
    have h0 := hc.lintegral_tile_lt_top μ 0
    have he : ∀ g : GL (Fin m) F, ‖c g * detPow g 0‖ₑ = ‖‖c g‖‖ₑ := fun g => by
      rw [detPow, Complex.cpow_zero, mul_one, enorm_norm]
    simp only [he] at h0
    exact h0
  have hpiece : ∀ k : ℕ, IntegrableOn (fun g => if ordDet g = (k : ℤ) then
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * c g else 0)
      (tile F m 0) μ := by
    intro k
    refine Integrable.mono' (hcint.const_mul BΦ) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · have hmeas : MeasurableSet {g : GL (Fin m) F | ordDet g = (k : ℤ)} :=
        (isClopen_shell F m k).isOpen.measurableSet
      have hcont : Continuous fun g : GL (Fin m) F =>
          Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * c g :=
        (hΦ.1.continuous.comp (Units.continuous_val.comp (continuous_const_mul _))).mul
          hc.continuous
      exact (hcont.aestronglyMeasurable.indicator hmeas).congr
        (Filter.Eventually.of_forall fun g => by simp [Set.indicator_apply])
    · split_ifs
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hBΦ _) (norm_nonneg _)
      · rw [norm_zero]; exact mul_nonneg hBΦ0 (norm_nonneg _)
  have hpt : ∀ g ∈ tile F m 0,
      Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        detPow (centralUnif F m ^ j * g) s * c (centralUnif F m ^ j * g) =
      (α * x ^ m) ^ j * ∑ k ∈ Finset.range m, x ^ k * (if ordDet g = (k : ℤ) then
        Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * c g else 0) := by
    intro g hg
    obtain ⟨hg0, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg0 hg1
    have hk : (ordDet g).toNat ∈ Finset.range m := Finset.mem_range.2 (by omega)
    rw [Finset.sum_eq_single_of_mem _ hk (fun k _ hk' => by
      rw [if_neg (by omega), mul_zero])]
    rw [if_pos (Int.toNat_of_nonneg hg0).symm, detPow_centralUnif_zpow_mul,
      IsCentralCoeff.zpow_mul hc, detPow_eq_qs_zpow, ← hx, mul_zpow, mul_comm j, _root_.zpow_mul,
      zpow_natCast, ← Int.toNat_of_nonneg hg0, zpow_natCast]
    simp only [Int.toNat_natCast]
    ring
  show ∫ g in tile F m 0, Φ ((centralUnif F m ^ j * g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      detPow (centralUnif F m ^ j * g) s * c (centralUnif F m ^ j * g) ∂μ = _
  rw [setIntegral_congr_fun (measurableSet_tile 0) hpt, integral_const_mul,
    integral_finsetSum _ (fun k _ => (hpiece k).const_mul _)]
  simp only [integral_const_mul, hPdef, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, hadef]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem IsCentralCoeff.lintegral_weight_lt_top (hc : IsCentralCoeff m α c)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {J : GL (Fin m) F → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞)
    (hJ : ∀ g, J g ≤ B * ENNReal.ofReal (min 1 (((LocalField.residueCard F : ℝ) ^ m) ^ ordDet g)))
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖) :
    ∫⁻ g, ‖c g * detPow g s‖ₑ * J g ∂μ < ∞ := by
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hqm : 1 ≤ q ^ m := one_le_pow₀ hq.le
  have hqm0 : 0 < q ^ m := by positivity
  set ρ : ℝ := ‖α * qs F s ^ m‖ with hρdef
  have hρ0 : 0 < ρ := norm_pos_iff.2 (mul_ne_zero hc.ne_zero (pow_ne_zero _ (qs_ne_zero s)))
  set K₁ := ∫⁻ g in tile F m 0, ‖c g * detPow g s‖ₑ ∂μ
  have hK₁ : K₁ ≠ ∞ := (hc.lintegral_tile_lt_top μ s).ne
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hval : ∀ (j : ℤ) (g : GL (Fin m) F),
      c (centralUnif F m ^ j * g) * detPow (centralUnif F m ^ j * g) s =
        (α * qs F s ^ m) ^ j * (c g * detPow g s) := by
    intro j g
    rw [detPow_centralUnif_zpow_mul, IsCentralCoeff.zpow_mul hc, mul_zpow, mul_comm j,
      _root_.zpow_mul, zpow_natCast]
    ring

  have hw : ∀ (j : ℤ) (g : GL (Fin m) F), g ∈ tile F m 0 →
      min 1 ((q ^ m) ^ ordDet (centralUnif F m ^ j * g)) ≤ min 1 ((q ^ m) ^ ((j + 1) * m)) := by
    intro j g hg
    obtain ⟨-, hg1⟩ := hg
    simp only [zero_mul, zero_add] at hg1
    refine min_le_min le_rfl (zpow_le_zpow_right₀ hqm ?_)
    rw [ordDet_centralUnif_zpow_mul]
    nlinarith
  rw [lintegral_eq_tsum_tile μ]
  set M : ℝ≥0∞ := B * K₁ * ENNReal.ofReal (max 1 ρ⁻¹)
  refine tsum_int_lt_top_of_le_geom₂ (M := M) (r₁ := ENNReal.ofReal ρ)
    (r₂ := ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hB hK₁) ENNReal.ofReal_ne_top)
    (ENNReal.ofReal_lt_one.2 hs) (ENNReal.ofReal_lt_one.2 ((div_lt_one hρ0).2 hs'))
    (fun k => ?_) (fun k => ?_)
  · calc ∫⁻ g in tile F m 0, ‖c (centralUnif F m ^ ((k : ℕ) : ℤ) * g) *
            detPow (centralUnif F m ^ ((k : ℕ) : ℤ) * g) s‖ₑ *
            J (centralUnif F m ^ ((k : ℕ) : ℤ) * g) ∂μ
        ≤ ∫⁻ g in tile F m 0, (B * ENNReal.ofReal ρ ^ k) * ‖c g * detPow g s‖ₑ ∂μ := by
          refine setLIntegral_mono' (measurableSet_tile 0) fun g hg => ?_
          rw [hval, enorm_mul, ← ofReal_norm, norm_zpow, ← hρdef, zpow_natCast,
            ENNReal.ofReal_pow hρ0.le]
          have hJg := hJ (centralUnif F m ^ ((k : ℕ) : ℤ) * g)
          have hmin : ENNReal.ofReal (min 1 ((q ^ m) ^ ordDet (centralUnif F m ^ ((k : ℕ) : ℤ) * g)))
              ≤ 1 := ENNReal.ofReal_le_one.2 (min_le_left _ _)
          calc ENNReal.ofReal ρ ^ k * ‖c g * detPow g s‖ₑ * J (centralUnif F m ^ ((k : ℕ) : ℤ) * g)
              ≤ ENNReal.ofReal ρ ^ k * ‖c g * detPow g s‖ₑ * (B * 1) := by
                gcongr
                exact hJg.trans (by gcongr)
            _ = _ := by ring
      _ = (B * ENNReal.ofReal ρ ^ k) * K₁ := lintegral_const_mul' _ _
            (ENNReal.mul_ne_top hB (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      _ ≤ M * ENNReal.ofReal ρ ^ k := by
          have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 ρ⁻¹) := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
          calc B * ENNReal.ofReal ρ ^ k * K₁ = B * K₁ * 1 * ENNReal.ofReal ρ ^ k := by ring
            _ ≤ B * K₁ * ENNReal.ofReal (max 1 ρ⁻¹) * ENNReal.ofReal ρ ^ k := by gcongr
  · set j : ℤ := -((k : ℤ) + 1) with hj
    have hr : (q ^ m) ^ ((j + 1) * m) = ((q ^ m) ^ (-(m : ℤ))) ^ k := by
      rw [hj, show (-((k : ℤ) + 1) + 1) * (m : ℤ) = -(m : ℤ) * k by ring, _root_.zpow_mul,
        zpow_natCast]
    have hρj : ρ ^ j = ρ⁻¹ * (ρ⁻¹) ^ k := by
      rw [hj, zpow_neg, zpow_add₀ hρ0.ne', zpow_one, zpow_natCast, mul_inv, mul_comm, inv_pow]
    calc ∫⁻ g in tile F m 0, ‖c (centralUnif F m ^ (-((k : ℤ) + 1)) * g) *
            detPow (centralUnif F m ^ (-((k : ℤ) + 1)) * g) s‖ₑ *
            J (centralUnif F m ^ (-((k : ℤ) + 1)) * g) ∂μ
        ≤ ∫⁻ g in tile F m 0, (B * ENNReal.ofReal (ρ⁻¹ * ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k)) *
            ‖c g * detPow g s‖ₑ ∂μ := by
          refine setLIntegral_mono' (measurableSet_tile 0) fun g hg => ?_
          rw [hval, enorm_mul, ← ofReal_norm, norm_zpow, ← hρdef, ← hj]
          have hJg := hJ (centralUnif F m ^ j * g)
          have hmin := ENNReal.ofReal_le_ofReal ((hw j g hg).trans (min_le_right _ _))
          rw [hr] at hmin
          calc ENNReal.ofReal (ρ ^ j) * ‖c g * detPow g s‖ₑ * J (centralUnif F m ^ j * g)
              ≤ ENNReal.ofReal (ρ ^ j) * ‖c g * detPow g s‖ₑ *
                  (B * ENNReal.ofReal (((q ^ m) ^ (-(m : ℤ))) ^ k)) := by
                gcongr
                exact hJg.trans (by gcongr)
            _ = _ := by
                have h1 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
                have h2 : 0 ≤ ρ⁻¹ ^ k := pow_nonneg h1 k
                have h3 : 0 ≤ ((q ^ m) ^ (-(m : ℤ))) ^ k := pow_nonneg (zpow_nonneg hqm0.le _) k
                rw [hρj, div_eq_mul_inv, mul_pow, ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h1,
                  ENNReal.ofReal_mul h3]
                ring
      _ = (B * ENNReal.ofReal (ρ⁻¹ * ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k)) * K₁ :=
            lintegral_const_mul' _ _ (ENNReal.mul_ne_top hB ENNReal.ofReal_ne_top)
      _ ≤ M * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hρ0.le), ENNReal.ofReal_pow (div_nonneg
            (zpow_nonneg (by positivity) _) hρ0.le)]
          have : ENNReal.ofReal ρ⁻¹ ≤ ENNReal.ofReal (max 1 ρ⁻¹) :=
            ENNReal.ofReal_le_ofReal (le_max_right _ _)
          calc B * (ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k) * K₁
              = B * K₁ * ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k := by ring
            _ ≤ B * K₁ * ENNReal.ofReal (max 1 ρ⁻¹) * ENNReal.ofReal ((q ^ m) ^ (-(m : ℤ)) / ρ) ^ k := by
                gcongr

end Integrals

end GodementJacquet

end GroundTheory.Automorphic
