import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RowsCompactSum

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem contFin : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pFin E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)

theorem contInf : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pInf E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)

theorem one_le (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (M : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal B * ENNReal.ofReal
      (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn (contInf (E := E) (k := k)).continuousOn
  refine ⟨(1 + max R 0) ^ M, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy), ← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 < (1 + ‖fun i => pInf E (y i)‖) ^ M := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h0, one_mul]
    apply pow_le_pow_left₀ (by positivity)
    have := hR y hy
    linarith [le_max_left R 0]
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem sum_le (hN : N0) (hG3 : ThetaSeriesBound) (hk : 1 ≤ k) (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (ha : k ≤ a) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ (g : GA E k) (r : ℝ), 0 < r → (∀ ξ, ξ ≠ 0 → r ≤ height g ξ) →
      ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
        ENNReal.ofReal (B * (C * (r ^ a)⁻¹)) := by
  have hCf : IsCompact ((fun y (i : Fin k) => pFin E (y i)) '' C₀) := hC₀.image contFin
  obtain ⟨M, C, hMC⟩ := hG3 E k _ hCf a ha
  obtain ⟨B, hB, hB1⟩ := one_le C₀ hC₀ M
  have hlast := (hN E k k hk le_rfl).2.2.2.2.2.2.2.2.2
  refine ⟨B, max C 0, hB, le_max_right _ _, fun g r hr hrh => ?_⟩
  have hinj : Function.Injective (fun ξ : RowT E k k => (⟨ξ.1, ξ.2.1⟩ : {ξ : Fin k → E // ξ ≠ 0})) := by
    intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  let F : {ξ : Fin k → E // ξ ≠ 0} → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))
  have hF : ∑' ξ, F ξ ≤ ENNReal.ofReal (C * (r ^ a)⁻¹) := hMC g r hr hrh
  have h1 : ∀ ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
      ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := by
    intro ξ
    rw [hlast]
    exact hB1 _
  calc _ ≤ ∑' ξ : RowT E k k, ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := ENNReal.tsum_le_tsum h1
    _ ≤ ∑' ξ, ENNReal.ofReal B * F ξ := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun ξ => ENNReal.ofReal B * F ξ)
    _ = ENNReal.ofReal B * ∑' ξ, F ξ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (max C 0 * (r ^ a)⁻¹) := by
        gcongr
        refine hF.trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (B * (max C 0 * (r ^ a)⁻¹)) := (ENNReal.ofReal_mul hB).symm

theorem r_le (hD : D0) (hK : K1) (hk : 1 ≤ k) (g : GA E k) :
    0 < dmin g * Dt g ^ ((k : ℝ)⁻¹) ∧ ∀ ξ, ξ ≠ 0 → dmin g * Dt g ^ ((k : ℝ)⁻¹) ≤ height g ξ := by
  have hDt := (hD E k).1 g
  have hK' := hK E k hk
  have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
  refine ⟨mul_pos (hK'.2.1 g) hp, fun ξ hξ => ?_⟩
  have h1 := hK'.2.2.1 g ξ hξ
  have h2 : height g ξ = ht g ξ * Dt g ^ ((k : ℝ)⁻¹) := by
    unfold ht; field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 hp.le

end RowsCompactSum

theorem rows_compact_of_bound : D0 → N0 → H0 → ThetaSeriesBound → K1 → RowsInCompactSet := by
  intro hD hN _ hG3 hK E _ _ _ k hk C₀ hC₀
  refine ⟨fun g => ?_, fun a ha => ?_⟩
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ k le_rfl
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hfin := h g _ hr hrh
    have hne : ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
    refine (ENNReal.finite_const_le_of_tsum_ne_top hne one_ne_zero).subset fun ξ hξ => ?_
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rw [Set.indicator_of_mem hξ]
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ a ha
    refine ⟨B * C, fun g => ?_⟩
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hDt := (hD E k).1 g
    have hd := (hK E k hk).2.1 g
    have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hw0 : 0 ≤ wt a g := by unfold wt; exact pow_nonneg (le_min zero_le_one hd.le) _
    have hw : wt a g ≤ dmin g ^ a := by unfold wt; exact pow_le_pow_left₀ (le_min zero_le_one hd.le) (min_le_right _ _) _
    calc (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) *
          ENNReal.ofReal (wt a g)
        ≤ ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * ENNReal.ofReal (wt a g) := by
          gcongr; exact h g _ hr hrh
      _ = ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹) * wt a g) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (B * C * Dt g ^ (-(a : ℝ) / k)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : Dt g ^ (-(a : ℝ) / k) = ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hDt.le, ← Real.rpow_neg hDt.le]
            congr 1; ring
          rw [he, mul_pow, mul_inv]
          have hda : 0 < dmin g ^ a := pow_pos hd _
          have hpa : 0 < (Dt g ^ ((k : ℝ)⁻¹)) ^ a := pow_pos hp _
          calc B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * wt a g
              ≤ B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * dmin g ^ a := by
                gcongr
            _ = B * C * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by field_simp

end PositivityTheory.AdelicQuotientData

end
