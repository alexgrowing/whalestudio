import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKEq2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem continuous_lastRow : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  unfold lastRow
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Continuous.matrix_elem Units.continuous_val i c
  · exact continuous_const

theorem lastRow_mir (p : GL (Fin k) E) (hp : IsMir (k - 1) p) (g : GA E k) :
    lastRow (ratGL E k p * g) = lastRow g := by
  funext c
  unfold lastRow
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have hrow : ∀ j, (ratGL E k p).val i j = (1 : Matrix (Fin k) (Fin k) (Ad E)) i j := by
      intro j
      have := hp i j (Or.inl (by omega))
      simp only [ratGL] at *
      simp [this, Matrix.one_apply]
    rw [Units.val_mul, Matrix.mul_apply]
    simp_rw [hrow]
    simp [Matrix.one_apply]
  · rfl

theorem measurable_sumF [Countable (RowT E k k)] {f : GA E k → ℂ} (hf : Continuous f)
    (hfin : ∀ g, {ξ : RowT E k k | f (ratGL E k (gam ξ) * g) ≠ 0}.Finite) : Measurable (sumF f) := by
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (RowT E k k)))
    (f := fun T g => ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g)) (fun T => ?_) ?_
  · exact Finset.measurable_sum _ fun ξ _ => (hf.comp (continuous_const.mul continuous_id)).measurable
  · rw [tendsto_pi_nhds]
    intro g
    have e : ∀ T : Finset (RowT E k k), (hfin g).toFinset ⊆ T →
        ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g) = sumF f g := by
      intro T hT
      unfold sumF
      rw [tsum_eq_sum (s := T)]
      intro b hb
      by_contra h
      exact hb (hT ((hfin g).mem_toFinset.2 h))
    exact tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨_, fun T hT => (e T hT).symm⟩)

theorem fin_bd {X : ℂ} {B C x y : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : ‖X‖ₑ ≤ ENNReal.ofReal B * ENNReal.ofReal (C * x)) : ‖X‖ ≤ B * max C 0 * y := by
  rw [← ENNReal.ofReal_mul hB, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff'] at h
  have h0 : C * x ≤ max C 0 * y :=
    calc C * x ≤ max C 0 * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ max C 0 * y := mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
  have h1 : B * (C * x) ≤ B * max C 0 * y := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h0 hB
  have h2 : 0 ≤ B * max C 0 * y := mul_nonneg (mul_nonneg hB (le_max_right _ _)) (hx.trans hxy)
  rcases h with h | h <;> linarith [norm_nonneg X]

theorem enorm_conj' (z : ℂ) : ‖conj z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]

end PKEq2

open PKEq2 in
theorem kernel_equality_second_of : D0 → N0 → H0 → ThetaDecaying → RowsInCompactSet → PoissonCutoffFormula → KEq2 := by
  intro hD0 hN0 hH0 hG4t hG5t hK12 E _ _ _ k hk ψ hψ S α' φ' hφ' U φ η s hcut hinv hcen
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -, hDinv, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, -, -, hcount, -, hperm, -⟩ := hN0 E k k hk le_rfl
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hinv' : ∀ γ g, φ (ratGL E k γ * g) = φ g := hinv
  have hinv2 : ∀ γ g, φ' (ratGL E k γ * g) = φ' g := hφ'.inv
  have hp1 : ∀ g : GA E k, (Dt g : ℂ) ^ (-(((k : ℂ) - k) / 2)) = 1 := fun g => by simp
  set V : (Fin k → Ad E) → XB E k := fun y => (η y : ℂ) • Rt E k (s y)⁻¹ φ with hV
  set F : GA E k → ℂ := fun g => (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹) with hF
  have hVc : Continuous V := hcut.contV
  have hVcpt : HasCompactSupport V := by
    have h1 : HasCompactSupport (fun y => (η y : ℂ)) := hcut.cpt.comp_left (g := Complex.ofReal) (by simp)
    exact h1.smul_right (f' := fun y => Rt E k (s y)⁻¹ φ)
  have hFV : ∀ x, F x = V (lastRow x) x := fun x => by simp [hF, hV]
  have hFc : Continuous F := by
    have : F = fun x => (V (lastRow x), x).1 (V (lastRow x), x).2 := funext hFV
    rw [this]
    exact continuous_eval.comp ((hVc.comp continuous_lastRow).prodMk continuous_id)
  have hFmir : ∀ p, IsMir (k - 1) p → ∀ x, F (ratGL E k p * x) = F x := by
    intro p hp x
    simp only [hF, lastRow_mir p hp, mul_assoc, hinv']
  have hsumInv : ∀ γ g, sumF F (ratGL E k γ * g) = sumF F g := by
    intro γ g
    obtain ⟨e, he⟩ := hperm γ
    unfold sumF
    rw [← e.tsum_eq (fun ξ => F (ratGL E k (gam ξ) * g))]
    refine tsum_congr fun ξ => ?_
    obtain ⟨p, hp, hpe⟩ := he ξ
    rw [← mul_assoc, ← map_mul, hpe, map_mul, mul_assoc, hFmir p hp]
  have hcpt : IsCompact (tsupport η) := hcut.cpt
  have hFzero : ∀ x, lastRow x ∉ tsupport η → F x = 0 := by
    intro x hx
    simp [hF, image_eq_zero_of_notMem_tsupport hx]
  have hfin : ∀ g, {ξ : RowT E k k | F (ratGL E k (gam ξ) * g) ≠ 0}.Finite := by
    intro g
    refine ((hG5t E k hk (tsupport η) hcpt).1 g).subset fun ξ hξ => ?_
    by_contra h
    exact hξ (hFzero _ h)
  have hSmeas : Measurable (sumF F) := measurable_sumF hFc hfin

  have hint : Integrable V (vecMeasure E (Fin k)) := hVc.integrable_of_hasCompactSupport hVcpt
  set W : XB E k := ∫ y, V y ∂vecMeasure E (Fin k) with hW
  have hI : ∀ g, (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k)) = W g := by
    intro g
    have := ContinuousLinearMap.integral_comp_comm (BoundedContinuousFunction.evalCLM ℂ g) hint
    rw [hW, ← BoundedContinuousFunction.evalCLM_apply (𝕜 := ℂ), ← this]
    simp [hV]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hp1, mul_one]
    exact hSmeas.mul (Complex.continuous_conj.comp φ'.continuous).measurable
  · simp only [hI]
    exact (W.continuous.mul (Complex.continuous_conj.comp φ'.continuous)).measurable
  · intro γ g
    simp only [hp1, mul_one]
    rw [hsumInv γ g, hinv2]
  · intro γ g
    simp only [mul_assoc, hinv', hinv2]
  · intro t g
    simp only [mul_assoc, hcen, hφ'.cen]
  · refine ⟨‖W‖ * ‖φ'‖, fun g => ?_⟩
    rw [hI, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (W.norm_coe_le_norm g) (φ'.norm_coe_le_norm g) (norm_nonneg _) (norm_nonneg _)
  · intro M
    obtain ⟨B, hB⟩ := hVc.bounded_above_of_compact_support hVcpt
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    obtain ⟨C, hC⟩ := (hG4t E k hk φ' hφ'.dec).2 (tsupport η) hcpt (k * M + k) (by nlinarith)
    refine ⟨B * max C 0, fun g hg => ?_⟩
    have hFbd : ∀ x, ‖F x‖ₑ ≤ ENNReal.ofReal B * (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow x) := by
      intro x
      by_cases hx : lastRow x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by rw [hFV]; exact ((V (lastRow x)).norm_coe_le_norm x).trans (hB _))
      · rw [Set.indicator_of_notMem hx, hFzero x hx]; simp
    set θ := ∑' ξ : RowT E k k, (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) with hθ
    have hS : ‖sumF F g‖ₑ ≤ ENNReal.ofReal B * θ :=
      enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hFbd _).trans_eq ENNReal.tsum_mul_left)
    have hx : Dt g ^ (-((k * M + k : ℕ) : ℝ) / k) ≤ (Dt g ^ M)⁻¹ := by
      have e : (-((k * M + k : ℕ) : ℝ) / k) = -(((M + 1 : ℕ) : ℝ)) := by push_cast; field_simp
      rw [e, Real.rpow_neg (hDpos g).le, Real.rpow_natCast]
      exact inv_anti₀ (pow_pos (hDpos g) _) (pow_le_pow_right₀ hg (by omega))
    refine fin_bd hB0 (Real.rpow_nonneg (hDpos g).le _) hx ?_
    simp only [hp1, mul_one]
    rw [enorm_mul, enorm_conj']
    calc ‖sumF F g‖ₑ * ‖φ' g‖ₑ ≤ (ENNReal.ofReal B * θ) * ‖φ' g‖ₑ := by gcongr
      _ = ENNReal.ofReal B * (θ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr; exact hC g
  · obtain ⟨Cf, hCf, hft⟩ := hcut.ft
    obtain ⟨M, C, hC⟩ := (hG4t E k hk (fun x => φ' (invT x)) hφ'.dec').1 Cf hCf k le_rfl
    obtain ⟨C', hC'⟩ := hft M
    refine ⟨max C' 0 * max C 0, fun g _ => ?_⟩
    have hJ : ∀ (z : Fin k → Ad E), ‖∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * z i) ∂vecMeasure E (Fin k)‖ₑ ≤
        ENNReal.ofReal (max C' 0) * ENNReal.ofReal (Cf.indicator (fun _ => ((1 + ‖fun i => pInf E (z i)‖) ^ M)⁻¹)
          fun i => pFin E (z i)) := by
      intro z
      have h := hC' z g
      by_cases hz : (fun i => pFin E (z i)) ∈ Cf
      · rw [Set.indicator_of_mem hz] at h ⊢
        rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      · rw [Set.indicator_of_notMem hz] at h ⊢
        rw [← ofReal_norm, le_antisymm h (norm_nonneg _)]
        simp
    have hgg : invT (invT g) = g := ((hH0 E k).2.2.2.2.2.2 g g).2
    have hCg := hC (invT g)
    simp only [hgg, hDinv] at hCg
    have e1 : ((Dt g)⁻¹) ^ (-(k : ℝ) / k) = Dt g := by
      rw [neg_div, div_self hk0, Real.rpow_neg_one, inv_inv]
    rw [e1] at hCg
    have hK : (Dt g : ℂ) * sumF F g = _ := hK12 E k hk ψ hψ S U φ η s hcut hinv g
    rw [hp1, mul_one, ← mul_assoc, hK, add_mul, add_sub_cancel_left]
    refine fin_bd (le_max_right _ _) (hDpos g).le le_rfl ?_
    rw [enorm_mul, enorm_conj']
    calc _ ≤ (ENNReal.ofReal (max C' 0) * ∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i))) * ‖φ' g‖ₑ := by
          gcongr
          exact enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hJ _).trans_eq ENNReal.tsum_mul_left)
      _ = ENNReal.ofReal (max C' 0) * (_ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr

end PositivityTheory.AdelicQuotientData

end
