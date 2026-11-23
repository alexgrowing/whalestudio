import Mathlib

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalProjection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
  {u : B → G}

structure IsProperHom (u : B → G) : Prop where
  continuous : Continuous u
  map_add : ∀ a b, u (a + b) = u a * u b
  isCompact_preimage : ∀ C : Set G, IsCompact C → IsCompact (u ⁻¹' C)

namespace IsProperHom

variable (hu : IsProperHom u)
include hu

theorem map_zero : u 0 = 1 := by
  have h := hu.map_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem map_neg_mul (b : B) (z : G) : u (-b) * (u b * z) = z := by
  rw [← mul_assoc, ← hu.map_add, neg_add_cancel, hu.map_zero, one_mul]

theorem isCompact_setOf_mul_mem {C : Set G} (hC : IsCompact C) (z : G) :
    IsCompact {b | u b * z ∈ C} :=
  (hu.isCompact_preimage _ (hC.image (continuous_mul_const z⁻¹))).of_isClosed_subset
    ((hC.isClosed.preimage (continuous_mul_const z)).preimage hu.continuous) fun b hb =>
      ⟨u b * z, hb, by simp⟩

end IsProperHom

def avgWeight (ν : Measure B) (u : B → G) (β : G → ℝ) (z : G) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal (β (u (-b) * z)) ∂ν

variable {ν : Measure B}

theorem measurable_avgWeight [SFinite ν] (hu : IsProperHom u) {β : G → ℝ} (hβ : Continuous β) :
    Measurable (avgWeight ν u β) := by
  have : Measurable fun p : B × G => ENNReal.ofReal (β (u (-p.1) * p.2)) :=
    ENNReal.measurable_ofReal.comp
      (hβ.comp ((hu.continuous.comp continuous_fst.neg).mul continuous_snd)).measurable
  exact this.lintegral_prod_left'

theorem avgWeight_mul_left [ν.IsAddLeftInvariant] (hu : IsProperHom u) (β : G → ℝ) (b' : B)
    (z : G) : avgWeight ν u β (u b' * z) = avgWeight ν u β z := by
  unfold avgWeight
  have h : ∀ b, u (-b) * (u b' * z) = u (-(b - b')) * z := fun b => by
    rw [← mul_assoc, ← hu.map_add, neg_sub, sub_eq_add_neg, add_comm b' (-b)]
  simp_rw [h]
  exact lintegral_sub_right_eq_self (fun b => ENNReal.ofReal (β (u (-b) * z))) b'

theorem avgWeight_lt_top [IsFiniteMeasureOnCompacts ν] (hu : IsProperHom u) {β : G → ℝ}
    (hβc : HasCompactSupport β) (hβ1 : ∀ x, β x ≤ 1) (z : G) : avgWeight ν u β z < ∞ := by
  set E := {b : B | u b * z ∈ tsupport β}
  have hE : IsCompact E := hu.isCompact_setOf_mul_mem hβc.isCompact z
  calc avgWeight ν u β z ≤ ∫⁻ b, (-E).indicator (fun _ => (1 : ℝ≥0∞)) b ∂ν := by
        refine lintegral_mono fun b => ?_
        by_cases hb : -b ∈ E
        · rw [indicator_of_mem (show b ∈ -E from hb)]
          exact ENNReal.ofReal_le_one.2 (hβ1 _)
        · rw [image_eq_zero_of_notMem_tsupport hb, ENNReal.ofReal_zero]
          exact (zero_le : (0 : ℝ≥0∞) ≤ _)
    _ = ν (-E) := lintegral_indicator_one hE.neg.isClosed.measurableSet
    _ < ∞ := hE.neg.measure_lt_top

theorem avgWeight_pos [ν.IsOpenPosMeasure] (hu : IsProperHom u) {β : G → ℝ} (hβ : Continuous β)
    {z : G} (hz : 0 < β z) : 0 < avgWeight ν u β z := by
  set U := {b : B | β z / 2 < β (u (-b) * z)}
  have hU : IsOpen U := isOpen_lt continuous_const
    (hβ.comp ((hu.continuous.comp continuous_neg).mul continuous_const))
  have h0 : (0 : B) ∈ U := by
    show β z / 2 < β (u (-0) * z)
    rw [neg_zero, hu.map_zero, one_mul]
    linarith
  have hUpos : 0 < ν U := hU.measure_pos ν ⟨0, h0⟩
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (β z / 2) * ν U :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by linarith)).ne' hUpos.ne'
    _ = ∫⁻ b in U, ENNReal.ofReal (β z / 2) ∂ν := by rw [setLIntegral_const]
    _ ≤ ∫⁻ b in U, ENNReal.ofReal (β (u (-b) * z)) ∂ν :=
        setLIntegral_mono' hU.measurableSet fun b hb => ENNReal.ofReal_le_ofReal (le_of_lt hb)
    _ ≤ avgWeight ν u β z := setLIntegral_le_lintegral _ _

variable {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]

set_option maxHeartbeats 1000000 in

theorem integral_mul_eq_zero_of_integral_eq_zero [ν.IsAddLeftInvariant] [SFinite ν]
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (hu : IsProperHom u) {h : G → ℂ}
    (hh : Continuous h) (hhc : HasCompactSupport h) {ψ : G → ℂ} (hψm : AEStronglyMeasurable ψ μ)
    (hψi : IntegrableOn ψ (tsupport h) μ) (hψu : ∀ b z, ψ (u b * z) = ψ z)
    (h0 : ∀ z, ∫ b, h (u b * z) ∂ν = 0) :
    ∫ z, h z * ψ z ∂μ = 0 := by
  obtain ⟨β, hβS, -, hβc, hβ01⟩ :=
    exists_continuous_one_zero_of_isCompact hhc.isCompact isClosed_empty (disjoint_empty _)
  set S := tsupport h with hSdef
  set c := avgWeight ν u β with hcdef
  have hβ1 : ∀ z ∈ S, β z = 1 := fun z hz => hβS hz
  have hc_pos : ∀ z ∈ S, 0 < c z := fun z hz =>
    avgWeight_pos hu β.continuous (by rw [hβ1 z hz]; norm_num)
  have hc_top : ∀ z, c z < ∞ := fun z => avgWeight_lt_top hu hβc (fun x => (hβ01 x).2) z
  have hcm : Measurable c := measurable_avgWeight hu β.continuous
  have hhz : ∀ z ∉ S, h z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz

  set w : B → G → ℝ≥0∞ := fun b z => ENNReal.ofReal (β (u (-b) * z)) / c z with hwdef
  have hwm : Measurable (uncurry fun z b => w b z) := by
    refine Measurable.div ?_ (hcm.comp measurable_fst)
    exact ENNReal.measurable_ofReal.comp
      (β.continuous.comp ((hu.continuous.comp continuous_snd.neg).mul continuous_fst)).measurable
  have hwm' : ∀ z, Measurable fun b => w b z := fun z =>
    hwm.comp (measurable_const.prodMk measurable_id)
  have hw_lt : ∀ z ∈ S, ∀ b, w b z < ∞ := fun z hz b =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top (hc_pos z hz).ne'
  have hw_int : ∀ z ∈ S, ∫⁻ b, w b z ∂ν = 1 := by
    intro z hz
    simp only [hwdef, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hc_pos z hz).ne')]
    exact ENNReal.mul_inv_cancel (hc_pos z hz).ne' (hc_top z).ne
  set Wt : B → G → ℝ := fun b z => (w b z).toReal with hWtdef
  have hW_int : ∀ z ∈ S, ∫ b, Wt b z ∂ν = 1 := by
    intro z hz
    rw [integral_toReal (hwm' z).aemeasurable (Eventually.of_forall (hw_lt z hz)), hw_int z hz,
      ENNReal.toReal_one]
  have hW_integrable : ∀ z ∈ S, Integrable (fun b => Wt b z) ν := fun z hz =>
    integrable_toReal_of_lintegral_ne_top (hwm' z).aemeasurable (by rw [hw_int z hz]; simp)
  have hW_nonneg : ∀ b z, 0 ≤ Wt b z := fun b z => ENNReal.toReal_nonneg
  set W₀ : G → ℝ := fun z => (ENNReal.ofReal (β z) / c z).toReal with hW₀def
  have hW₀ : ∀ b z, Wt b (u b * z) = W₀ z := by
    intro b z
    simp only [hWtdef, hwdef, hW₀def, hu.map_neg_mul, hcdef, avgWeight_mul_left hu]

  set F : G → B → ℂ := fun z b => h z * ψ z * (Wt b z : ℂ) with hFdef
  have hhψ : Integrable (fun z => h z * ψ z) μ := by
    have h1 : IntegrableOn (fun z => h z * ψ z) S μ :=
      hψi.continuousOn_mul hh.continuousOn hhc.isCompact
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
    intro z hz
    by_contra hzS
    exact hz (by simp [hhz z hzS])
  have hFm : AEStronglyMeasurable (uncurry F) (μ.prod ν) := by
    refine ((hh.comp continuous_fst).aestronglyMeasurable.mul
      (hψm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)).mul ?_
    exact (Complex.continuous_ofReal.measurable.comp
      (ENNReal.measurable_toReal.comp hwm)).aestronglyMeasurable
  have hFint : Integrable (uncurry F) (μ.prod ν) := by
    refine (integrable_prod_iff hFm).2 ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · by_cases hz : z ∈ S
      · exact ((hW_integrable z hz).ofReal).const_mul (h z * ψ z)
      · simp only [uncurry_apply_pair, hFdef, hhz z hz, zero_mul]
        exact integrable_zero _ _ _
    · refine hhψ.norm.congr (Eventually.of_forall fun z => ?_)
      simp only [uncurry_apply_pair, hFdef]
      by_cases hz : z ∈ S
      · have : ∀ b, ‖h z * ψ z * (Wt b z : ℂ)‖ = ‖h z * ψ z‖ * Wt b z := fun b => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW_nonneg b z)]
        simp_rw [this]
        rw [integral_const_mul, hW_int z hz, mul_one]
      · simp [hhz z hz]

  set F' : B → G → ℂ := fun b z => h (u b * z) * ψ z * (W₀ z : ℂ) with hF'def
  have hΦ : MeasurePreserving (fun p : B × G => (p.1, u p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun b z => u b * z)
      ((hu.continuous.comp continuous_fst).mul continuous_snd).measurable
      (Eventually.of_forall fun b => map_mul_left_eq_self μ (u b))
  have hF'int : Integrable (uncurry F') (ν.prod μ) := by
    have hs : Integrable (uncurry F ∘ Prod.swap) (ν.prod μ) := hFint.swap
    have h2 := (hΦ.integrable_comp hs.aestronglyMeasurable).2 hs
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only [comp_apply, Prod.swap, uncurry_apply_pair, hFdef, hF'def, hψu, hW₀]
    rfl
  calc ∫ z, h z * ψ z ∂μ = ∫ z, ∫ b, F z b ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hFdef]
        by_cases hz : z ∈ S
        · rw [integral_const_mul, integral_complex_ofReal, hW_int z hz, Complex.ofReal_one, mul_one]
        · simp [hhz z hz]
    _ = ∫ b, ∫ z, F z b ∂μ ∂ν := integral_integral_swap hFint
    _ = ∫ b, ∫ z, F' b z ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun b => ?_)
        dsimp only
        rw [← integral_mul_left_eq_self (fun z => F z b) (u b)]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hFdef, hF'def, hψu, hW₀]
    _ = ∫ z, ∫ b, F' b z ∂ν ∂μ := integral_integral_swap hF'int
    _ = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
        simp only [hF'def, mul_assoc, Pi.zero_apply]
        rw [integral_mul_const, h0 z, zero_mul]

end CuspidalProjection

end

end GroundTheory.Automorphic
