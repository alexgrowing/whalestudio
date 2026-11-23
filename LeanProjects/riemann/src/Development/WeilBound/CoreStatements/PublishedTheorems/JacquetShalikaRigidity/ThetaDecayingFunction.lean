import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ThetaDecayingFunction

theorem key {x C1 D : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D) :
    ((D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * x = C1 * D ^ (-(a : ℝ) / k) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hD.le, Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha,
    show -(a : ℝ) / k = -((k : ℝ)⁻¹ * a) by ring, Real.rpow_neg hD.le]
  have : 0 < D ^ ((k : ℝ)⁻¹ * a) := Real.rpow_pos_of_pos hD _
  field_simp

theorem le_height {x C1 D h : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D)
    (ht : 0 < h / D ^ ((k : ℝ)⁻¹)) (hb : x ≤ C1 * (h / D ^ ((k : ℝ)⁻¹)) ^ a) :
    D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹) ≤ h := by
  have hDk : 0 < D ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hD _
  have h1 : (x / C1) ^ ((a : ℝ)⁻¹) ≤ h / D ^ ((k : ℝ)⁻¹) := by
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (div_nonneg hx.le hC.le) _) ht.le ha,
      Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha, div_le_iff₀' hC]
    exact hb
  calc _ ≤ D ^ ((k : ℝ)⁻¹) * (h / D ^ ((k : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h1 hDk.le
    _ = h := by field_simp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem part1 (hD : D0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (Cf : Set (Fin k → Af E)) (hCf : IsCompact Cf) (a : ℕ) (hka : k ≤ a) :
    ∃ (M : ℕ) (C : ℝ), ∀ g : GA E k, (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  obtain ⟨M, C, hMC⟩ := hG E k Cf hCf a hka
  obtain ⟨C1, hC1⟩ := hφ a
  refine ⟨M, C * C1, fun g => ?_⟩
  have hDg : 0 < Dt g := (hD E k).1 g
  by_cases h0 : φ g = 0
  · simp [h0]
  have hx : 0 < ‖φ g‖ := norm_pos_iff.2 h0
  have hne : (fun _ : Fin k => (1 : E)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hk⟩
    simp at this
  have hC1p : 0 < C1 := by
    have h1 := hC1 g _ hne
    have h2 := (hH E k).1 g _ hne
    by_contra hc
    replace hc := not_lt.1 hc
    have : C1 * ht g (fun _ => 1) ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg h2.le _)
    linarith
  have ha : a ≠ 0 := by omega
  have hr : 0 < Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹) :=
    mul_pos (Real.rpow_pos_of_pos hDg _) (Real.rpow_pos_of_pos (div_pos hx hC1p) _)
  have hbound := hMC g _ hr fun ξ hξ => le_height ha hx hC1p hDg ((hH E k).1 g ξ hξ) (hC1 g ξ hξ)
  calc _ ≤ ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹) * ‖φ g‖ₑ := by
        gcongr
    _ = ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * ‖φ g‖) := by
        rw [ENNReal.ofReal_mul' (norm_nonneg _), ofReal_norm]
    _ = _ := by rw [mul_assoc, key ha hx hC1p hDg, mul_assoc]

theorem ind_le {C₀ : Set (Fin k → Ad E)} {R : ℝ} (hR : ∀ y ∈ C₀, ‖fun i => pInf E (y i)‖ ≤ R) (M : ℕ)
    (y : Fin k → Ad E) :
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal ((1 + max R 0) ^ M) *
      ENNReal.ofReal (((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal, ← div_eq_mul_inv,
      one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith [hR y hy, le_max_left R 0]) M
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem part2 (hD : D0) (hN : N0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (hka : k ≤ a) :
    ∃ C : ℝ, ∀ g : GA E k,
      (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  have hcF : Continuous fun y : Fin k → Ad E => fun i => pFin E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pFin E).comp (continuous_apply i)
  have hcI : Continuous fun y : Fin k → Ad E => fun i => pInf E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pInf E).comp (continuous_apply i)
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn hcI.continuousOn
  obtain ⟨M, C', hC'⟩ := part1 hD hH hG hk φ hφ _ (hC₀.image hcF) a hka
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hN E k k hk le_rfl
  let e : {ξ : Fin k → E // ξ ≠ 0} ≃ RowT E k k :=
    { toFun := fun ξ => ⟨ξ.1, ξ.2, fun i hi => absurd i.2 (by omega)⟩
      invFun := fun ξ => ⟨ξ.1, ξ.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hK : (0 : ℝ) ≤ (1 + max R 0) ^ M := by positivity
  refine ⟨(1 + max R 0) ^ M * C', fun g => ?_⟩
  rw [← e.tsum_eq]
  calc _ = (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, C₀.indicator (fun _ => (1 : ℝ≥0∞))
          ((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val)) * ‖φ g‖ₑ := by
        congr 1
        exact tsum_congr fun ξ => by rw [hlast]; rfl
    _ ≤ (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ :=
        by
        gcongr with ξ
        exact ind_le hR M _
    _ = ENNReal.ofReal ((1 + max R 0) ^ M) * ((∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ) := by
        rw [ENNReal.tsum_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (C' * Dt g ^ (-(a : ℝ) / k)) :=
        by
        gcongr
        exact hC' g
    _ = _ := by rw [← ENNReal.ofReal_mul hK, mul_assoc]

end ThetaDecayingFunction

theorem theta_decaying_of_bound : D0 → N0 → H0 → ThetaSeriesBound → ThetaDecaying := by
  intro hD hN hH hG E _ _ _ k hk φ hφ
  exact ⟨fun Cf hCf a hka => ThetaDecayingFunction.part1 hD hH hG hk φ hφ Cf hCf a hka,
    fun C₀ hC₀ a hka => ThetaDecayingFunction.part2 hD hN hH hG hk φ hφ C₀ hC₀ a hka⟩

end PositivityTheory.AdelicQuotientData

end
