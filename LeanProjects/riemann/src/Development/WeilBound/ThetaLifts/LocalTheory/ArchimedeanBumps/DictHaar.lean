import Mathlib

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {ι : Type} [Fintype ι]

theorem map_mul_vol (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) :
    Measure.map (fun c : ι → ℂ => s * c) volume = ENNReal.ofReal (∏ w, ‖s w‖ ^ 2)⁻¹ • volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun i => (LinearMap.mul ℝ ℂ (s i)).comp (LinearMap.proj i)
  have hd : LinearMap.det f = ∏ w, ‖s w‖ ^ 2 := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := Algebra.norm_apply ℝ (s i)
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq] at this
    exact this.symm
  have hp : 0 < ∏ w, ‖s w‖ ^ 2 := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hs w)) 2
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := f) (by rw [hd]; exact hp.ne')
  rw [hd, abs_of_pos (inv_pos.2 hp)] at this
  exact this

def dens (c : ι → ℂ) : ℝ≥0 := ⟨(∏ w, ‖c w‖ ^ 2)⁻¹, by positivity⟩

theorem measurable_dens : Measurable (dens : (ι → ℂ) → ℝ≥0) := by
  refine Measurable.subtype_mk ?_
  fun_prop

theorem ae_ne : ∀ᵐ c : ι → ℂ, ∀ w, c w ≠ 0 := by
  rw [ae_all_iff]
  intro w
  exact (Measure.quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure ℂ)) w).ae (p := fun z => z ≠ 0)
    (by rw [ae_iff]; simp)

theorem dens_inv (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) (A : Set (ι → ℂ)) (hA : MeasurableSet A) :
    volume.withDensity (fun c => (dens c : ℝ≥0∞)) ((fun c => s * c) ⁻¹' A) = volume.withDensity (fun c => (dens c : ℝ≥0∞)) A := by
  have hm : Measurable fun c : ι → ℂ => s * c := by fun_prop
  have hp : 0 < ∏ w, ‖s w‖ ^ 2 := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hs w)) 2
  have hd : Measurable fun c : ι → ℂ => (dens c : ℝ≥0∞) := measurable_dens.coe_nnreal_ennreal
  rw [withDensity_apply _ (hm hA), withDensity_apply _ hA, ← lintegral_indicator (hm hA), ← lintegral_indicator hA]
  have e : ∀ c, ((fun c => s * c) ⁻¹' A).indicator (fun c => (dens c : ℝ≥0∞)) c =
      ENNReal.ofReal (∏ w, ‖s w‖ ^ 2) * A.indicator (fun c => (dens c : ℝ≥0∞)) (s * c) := by
    intro c
    by_cases h : s * c ∈ A
    · rw [indicator_of_mem (show c ∈ (fun c => s * c) ⁻¹' A from h), indicator_of_mem h, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hp.le]
      congr 1
      change (∏ w, ‖c w‖ ^ 2)⁻¹ = (∏ w, ‖s w‖ ^ 2) * (∏ w, ‖(s * c) w‖ ^ 2)⁻¹
      simp only [Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib, mul_inv]
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    · rw [indicator_of_notMem (show c ∉ (fun c => s * c) ⁻¹' A from h), indicator_of_notMem h, mul_zero]
  simp only [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_map (hd.indicator hA) hm, map_mul_vol s hs,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one,
    one_mul]

theorem haar_units {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (j : G → ι → ℂ) (hj : IsOpenEmbedding j) (hr : range j = {c | ∀ w, c w ≠ 0}) (hm : ∀ a b, j (a * b) = j a * j b)
    (x : Measure G) [x.IsHaarMeasure] : ∃ κ : ℝ, 0 < κ ∧ ∀ g : (ι → ℂ) → ℂ,
      ∫ l, g (j l) ∂x = κ * ∫ c, g c * ((∏ w, ‖c w‖ ^ 2 : ℝ) : ℂ)⁻¹ := by
  haveI := hj.locallyCompactSpace
  haveI := hj.isEmbedding.secondCountableTopology
  have he := hj.measurableEmbedding
  let ν : Measure (ι → ℂ) := volume.withDensity fun c => (dens c : ℝ≥0∞)
  let y : Measure G := ν.comap j
  have hy : ∀ A, y A = ν (j '' A) := fun A => he.comap_apply ν A
  have hne : ∀ a w, j a w ≠ 0 := fun a => (hr ▸ mem_range_self a : j a ∈ {c : ι → ℂ | ∀ w, c w ≠ 0})
  haveI : y.IsMulLeftInvariant := ⟨fun g => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul g) hA, hy, hy, ← dens_inv (j g) (hne g) _ (he.measurableSet_image' hA)]
    congr 1
    ext c
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g * a, ha, hm g a⟩
    · rintro ⟨a, ha, e⟩
      refine ⟨g⁻¹ * a, by simpa using ha, ?_⟩
      have h1 : j g * j (g⁻¹ * a) = j g * c := by rw [← hm, mul_inv_cancel_left]; exact e
      funext w
      exact mul_left_cancel₀ (hne g w) (congrFun h1 w)⟩
  haveI : IsFiniteMeasureOnCompacts y := ⟨fun K hK => by
    have hc := hK.image hj.continuous
    rw [hy, withDensity_apply _ hc.measurableSet]
    have hco : ContinuousOn (fun c : ι → ℂ => (dens c : ℝ)) (j '' K) := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      rintro _ ⟨a, _, rfl⟩
      exact (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hne a w)) 2).ne'
    exact (hasFiniteIntegral_iff_ofNNReal).1 (hco.integrableOn_compact hc).2⟩
  haveI : y.IsOpenPosMeasure := ⟨fun O hO hn h => by
    rw [hy, withDensity_apply_eq_zero measurable_dens.coe_nnreal_ennreal] at h
    have : {c | (dens c : ℝ≥0∞) ≠ 0} ∩ j '' O = j '' O := by
      refine inter_eq_right.2 ?_
      rintro _ ⟨a, _, rfl⟩ h0
      have h1 : (dens (j a) : ℝ) = 0 := by exact_mod_cast (ENNReal.coe_eq_zero.1 h0)
      exact (inv_pos.2 (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hne a w)) 2)).ne' h1
    rw [this] at h
    exact (hj.isOpenMap O hO).measure_ne_zero volume (hn.image j) h⟩
  haveI : y.IsHaarMeasure := {}
  refine ⟨Measure.haarScalarFactor x y, by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure x y, fun g => ?_⟩
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul x y]
  have hν : ν.restrict {c | ∀ w, c w ≠ 0} = volume.withDensity fun c => (dens c : ℝ≥0∞) :=
    Measure.restrict_eq_self_of_ae_mem ((withDensity_absolutelyContinuous _ _).ae_le ae_ne)
  rw [integral_smul_nnreal_measure, ← he.integral_map, he.map_comap, hr, hν,
    integral_withDensity_eq_integral_smul measurable_dens, NNReal.smul_def, Complex.real_smul]
  congr 2
  funext c
  rw [NNReal.smul_def, Complex.real_smul, mul_comm, ← Complex.ofReal_inv]
  rfl

end PositivityTheory.ThKG.Loc.Bump

end
