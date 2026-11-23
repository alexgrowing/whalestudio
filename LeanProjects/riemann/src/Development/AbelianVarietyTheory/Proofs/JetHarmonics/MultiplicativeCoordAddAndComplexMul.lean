import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RingHomPointBijective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubstStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChartStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallPointMultiplicativeCoordinateExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslateStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPointStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.AtAdd

variable {q : ℕ} [Fact q.Prime]

open Classical in

theorem sub_mem_of_uw (M : Mdl q) (hM : M.Ok) (s t : ℂ) (ht : t ∉ M.L.lattice) (hy : M.y t ≠ 0)
    (hu : M.u s = M.u t) (hw : M.w s = M.w t) : s - t ∈ M.L.lattice := by
  have hwt : M.w t = -1 / M.y t := by simp [Mdl.w, ht]
  have hwt0 : M.w t ≠ 0 := by rw [hwt]; exact div_ne_zero (by norm_num) hy
  have hs : s ∉ M.L.lattice := by
    intro hs
    apply hwt0
    rw [← hw]; simp [Mdl.w, hs]
  have hws : M.w s = -1 / M.y s := by simp [Mdl.w, hs]
  have hys : M.y s ≠ 0 := by
    intro h
    apply hwt0
    rw [← hw, hws, h, div_zero]
  have hyy : M.y s = M.y t := by
    rw [hws, hwt, div_eq_div_iff hys hy] at hw
    linear_combination hw
  have hxx : M.x s = M.x t := by
    have h1 : M.u s = -M.x s / M.y s := by simp [Mdl.u, hs]
    have h2 : M.u t = -M.x t / M.y t := by simp [Mdl.u, ht]
    rw [h1, h2, hyy, div_left_inj' hy] at hu
    exact neg_injective hu
  obtain ⟨φ, -, hk, hφ⟩ := Mdl.exists_pointHom q M hM
  obtain ⟨h1, e1⟩ := hφ s hs
  obtain ⟨h2, e2⟩ := hφ t ht
  rw [← hk, map_sub, e1, e2, sub_eq_zero]
  congr 1 <;> simp [hxx, hyy]

theorem sub_mem_of_germ (M : Mdl q) (hM : M.Ok) (α s t : ℂ) (hα : α ≠ 0) (ht : M.Small t)
    (hu : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u (α * z + s) = M.u (α * z + t))
    (hw : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.w (α * z + s) = M.w (α * z + t)) : s - t ∈ M.L.lattice := by
  have hg := ((uw_elliptic_flow q M hM).2.2.2.2.2.2.2.2 t ht).2.2.2.2.1
  have htend : Filter.Tendsto (fun z : ℂ => α * z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous (fun z : ℂ => α * z + t) := by fun_prop
      simpa using hc.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [hα] using hz
  obtain ⟨z, h1, h2, h3⟩ := ((htend.eventually hg).and (hu.and hw)).exists
  have := sub_mem_of_uw M hM _ _ h1.1 h1.2.1 h2 h3
  simpa using this

theorem const_ell (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  simp [logS, ← coeff_zero_eq_constantCoeff_apply]

theorem bd_w (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (h : M.Chart ℓ) : Bd 1 (hat M.ι ℓ M.w) := by
  obtain ⟨-, v, xs, ys, -, -, hys, -, -, hc, -, hw, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M ℓ h
  apply (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 hys hc
  rw [pow_zero, one_mul, mul_comm, hw]
  intro n
  rw [map_neg, norm_neg, coeff_X_pow]
  split_ifs <;> simp

theorem germ_add (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (ζ ζ' : ℂ_[q]) (p p' t : ℂ) (h : M.At ω ζ p) (h' : M.At ω ζ' p') (ht : M.At ω (ζ * ζ') t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (1 * z + (p + p')) = F (1 * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hEp : Ell M.L (fun z => F (z + p)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (x + p)).comp_analyticAt (f := F) (g := fun z => z + p) (by fun_prop)
    · show F (z + l + p) = F (z + p)
      rw [add_right_comm, hE.2 l hl]
  have hBp : Bdd (hat M.ι (C ω * logS) (fun z => F (z + p))) := by
    rw [hT ζ p h]
    exact ⟨1, (Shift.shift_laws q ζ h.2.1).1 _ _ hB⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ' p' _ hM h' hEp (han p h.1) hBp
  rw [hT ζ p h, (GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).1 ζ' ζ _ h'.2.1 h.2.1 ⟨1, hB⟩, mul_comm ζ' ζ, ← hT _ t ht] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa (han t ht.1)).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [one_mul, ← e2, e1]
  congr 1; ring

theorem germ_mul (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p t : ℂ)
    (hL : ∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) (hα : M.ι α = zc a)
    (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hζ : ζ ^ (q ^ n) = 1)
    (h : M.At ω ζ p) (ht : M.At ω (ζ ^ k) t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (α * z + α * p) = F (α * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hF0 : AnalyticAt ℂ F 0 := hA 0 (Or.inl (zero_mem _))
  have hmul : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → AnalyticAt ℂ (fun z => G (α * z)) 0 := fun G hG =>
    AnalyticAt.comp_of_eq (g := G) (f := fun z => α * z) hG (by fun_prop) (by simp)
  have hEα : Ell M.L (fun z => F (α * z)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (α * x)).comp_analyticAt (f := F) (g := fun z => α * z) (by fun_prop)
    · show F (α * (z + l)) = F (α * z)
      rw [mul_add, hE.2 _ (hL l hl)]
  have hsub := (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω F hF0).2.2.1 α a hα
  have hm := (MulSeries.mulS_laws q).1 a
  have hBα : Bdd (hat M.ι (C ω * logS) (fun z => F (α * z))) := by
    rw [hsub]
    exact ⟨1, (sup_norm_laws q).2.1 _ _ _ hB hm.1 hm.2.1⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ p _ hM h hEα (hmul F hF0) hBα
  rw [hsub, ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ζ n k a _ hζ hk ⟨1, hB⟩).2, ← hT _ t ht,
    ← (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω _ (han t ht.1)).2.2.1 α a hα] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa
    (hmul _ (han t ht.1))).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [← mul_add, ← e1, e2]

theorem norm_mul_sub_one_lt {ζ ξ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (h' : ‖ξ - 1‖ < 1) : ‖ζ * ξ - 1‖ < 1 := by
  have e : ζ * ξ - 1 = (ζ - 1) * (ξ - 1) + ((ζ - 1) + (ξ - 1)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h h'.le
  · exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h h')

theorem norm_pow_sub_one_lt {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (k : ℕ) : ‖ζ ^ k - 1‖ < 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih h

theorem at_add_and_mul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  intro q _ M ω hM
  have hOk : M.Ok := hM.1
  obtain ⟨hex, -, -, hiff, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨hEu, hEw, -, -, -, -, -, -, hS⟩ := uw_elliptic_flow q M hOk
  have hBu : Bd 1 (hat M.ι (C ω * logS) M.u) := hM.2.2.1
  have hBw := bd_w M _ hM
  have hTu := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).1
  have hTw := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).2
  refine ⟨fun ζ ζ' p p' h h' => ?_, fun α a n k ζ p hL hα hk hζ h => ?_⟩
  · obtain ⟨t, ht⟩ := hex _ (norm_mul_sub_one_lt h.2.1 h'.2.1)
    have := sub_mem_of_germ M hOk 1 (p + p') t one_ne_zero ht.1
      (germ_add M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu ζ ζ' p p' t h h' ht)
      (germ_add M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw ζ ζ' p p' t h h' ht)
    refine (hiff _ t _ ht).2 ?_
    simpa using neg_mem this
  · by_cases h0 : α = 0
    · subst h0
      have ha : a = 0 := by
        have := (MulSeries.mulS_laws q).2.2.2.2.2 a
        rw [← hα, map_zero, norm_zero] at this
        exact norm_eq_zero.1 this.symm
      subst ha
      rw [zero_sub, norm_neg] at hk
      have hd : ((q : ℤ) ^ n) ∣ (k : ℤ) := by
        rw [← PadicInt.norm_int_le_pow_iff_dvd]
        simpa using hk
      have hd' : q ^ n ∣ k := by exact_mod_cast hd
      obtain ⟨m, rfl⟩ := hd'
      rw [pow_mul, hζ, one_pow, zero_mul]
      exact h10
    · obtain ⟨t, ht⟩ := hex _ (norm_pow_sub_one_lt h.2.1 k)
      have := sub_mem_of_germ M hOk α (α * p) t h0 ht.1
        (germ_mul M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu α a n k ζ p t hL hα hk hζ h ht)
        (germ_mul M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw α a n k ζ p t hL hα hk hζ h ht)
      refine (hiff _ t _ ht).2 ?_
      simpa using neg_mem this

end GlobalTheory.MomOne.AtAdd
