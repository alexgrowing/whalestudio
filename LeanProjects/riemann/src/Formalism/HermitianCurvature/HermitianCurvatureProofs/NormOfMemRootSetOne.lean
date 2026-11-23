import Formalism.HermitianCurvature.HermitianCurvatureProofs.RootPushforwardDensity
import Formalism.HermitianCurvature.StatementG

namespace Formalism.FourierDecayAlt.P.PBK

open MeasureTheory Filter Topology Set Polynomial

noncomputable section

open Classical

theorem mem_rootSet' {s : ℕ} (hs : s ≠ 0) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hs)]

theorem one_mem_rootSet_one {s : ℕ} (hs : s ≠ 0) : (1 : ℂ) ∈ G.rootSet s 1 := by
  exact (Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mpr (one_pow s)

theorem norm_of_mem_rootSet_one {s : ℕ} (hs : s ≠ 0) {ζ : ℂ} (hζ : ζ ∈ G.rootSet s 1) : ‖ζ‖ = 1 := by
  exact Complex.norm_eq_one_of_pow_eq_one ((Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mp hζ) hs

theorem rootSet_mul_eq {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0) (hz : z ^ s = w) (hρ : ρ ^ s = l)
    (hl : l ≠ 0) : G.rootSet s (l * w) = (G.rootSet s 1).image (fun ζ => ζ * ρ * z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hz, zero_pow hs])
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hl (by rw [← hρ, zero_pow hs])
  ext y
  rw [Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs, Finset.mem_image]
  constructor
  · intro hy
    refine ⟨y / (ρ * z), (Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mpr ?_, ?_⟩
    · rw [div_pow, mul_pow, hρ, hz, hy, div_self (mul_ne_zero hl hw)]
    · field_simp
  · rintro ⟨ζ, hζ, rfl⟩
    rw [Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs] at hζ
    rw [mul_pow, mul_pow, hζ, hρ, hz, one_mul]

theorem injOn_rootSet_mul {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0) (hz : z ^ s = w) (hρ : ρ ^ s = l)
    (hl : l ≠ 0) : Set.InjOn (fun ζ => ζ * ρ * z) (G.rootSet s 1 : Set ℂ) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hz, zero_pow hs])
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hl (by rw [← hρ, zero_pow hs])
  intro ζ _ ζ' _ h
  exact mul_right_cancel₀ hρ0 (mul_right_cancel₀ hz0 h)

theorem sum_rootSet_mul {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0)
    (hz : z ^ s = w) (hρ : ρ ^ s = l) (hl : l ≠ 0) (Gf : ℂ → E) :
    ∑ y ∈ G.rootSet s (l * w), Gf y = ∑ ζ ∈ G.rootSet s 1, Gf (ζ * ρ * z) := by
  rw [Formalism.FourierDecayAlt.P.PBK.rootSet_mul_eq hs hw hz hρ hl,
    Finset.sum_image fun x hx y hy h => Formalism.FourierDecayAlt.P.PBK.injOn_rootSet_mul hs hw hz hρ hl hx hy h]

theorem sum_rootSet_eq_range {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w : ℂ} (hw : w ≠ 0)
    (F : ℂ → E) : ∑ z ∈ G.rootSet s w, F z = ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k w) := by
  have hnd := (Complex.isPrimitiveRoot_exp s hs).nthRoots_nodup hw
  rw [G.rootSet, ← Multiset.toFinset_eq hnd]
  show (Multiset.map F (nthRoots s w)).sum = _
  rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.nthRoots_eq_R s hs w, Multiset.map_map]
  rfl

section change

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rootBranch (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (F : ℂ → E)
    (hF : Integrable (fun z => ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z)) :
    Integrable (fun c => F (NthRootMeasurability.R s k (u * c))) ∧
      ∫ c, F (NthRootMeasurability.R s k (u * c)) = ∫ z in NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
  have hA : MeasurableSet (NthRootMeasurability.A s k) := Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A s k

  have hderiv : ∀ z ∈ NthRootMeasurability.A s k, HasFDerivWithinAt (fun z => u⁻¹ * z ^ s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ)
      (NthRootMeasurability.A s k) z := fun z _ =>
    (((hasDerivAt_pow s z).const_mul u⁻¹).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj := Formalism.FourierDecayAlt.P.NthRootMeasurability.injOn_A s k u hu
  have himg := Formalism.FourierDecayAlt.P.NthRootMeasurability.image_A s k hs u hu
  have hdet : ∀ z : ℂ, |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ).det| = ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 := fun z => by
    rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.detC, abs_of_nonneg (by positivity)]
  have hback : ∀ z ∈ NthRootMeasurability.A s k, F (NthRootMeasurability.R s k (u * (u⁻¹ * z ^ s))) = F z := fun z hz => by
    rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul, hz.2]
  have hnull : (volume : Measure ℂ).restrict ({0}ᶜ : Set ℂ) = volume := MeasureTheory.restrict_compl_singleton 0
  constructor
  · have h1 : IntegrableOn (fun c => F (NthRootMeasurability.R s k (u * c))) ((fun z => u⁻¹ * z ^ s) '' NthRootMeasurability.A s k) := by
      rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hA hderiv hinj]
      refine (hF.integrableOn (s := NthRootMeasurability.A s k)).congr_fun (fun z hz => ?_) hA
      simp only [hdet, hback z hz]
    rw [himg, IntegrableOn, hnull] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_det_fderiv_smul volume hA hderiv hinj
      (fun c => F (NthRootMeasurability.R s k (u * c)))
    rw [himg, hnull] at h2
    rw [h2]
    refine setIntegral_congr_fun hA (fun z hz => ?_)
    simp only [hdet, hback z hz]

theorem integral_sum_rootSet (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (F : ℂ → E)
    (hF : Integrable (fun z => ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z)) :
    Integrable (fun c => ∑ z ∈ G.rootSet s (u * c), F z) ∧
      ∫ c, ∑ z ∈ G.rootSet s (u * c), F z = ∫ z, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
  have hae : ∀ᵐ c : ℂ, c ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)

  have hsum : (fun c => ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k (u * c))) =ᵐ[volume]
      fun c => ∑ z ∈ G.rootSet s (u * c), F z := by
    filter_upwards [hae] with c hc
    rw [Formalism.FourierDecayAlt.P.PBK.sum_rootSet_eq_range hs (mul_ne_zero hu hc)]
  have hbr := fun k => Formalism.FourierDecayAlt.P.PBK.rootBranch s k hs u hu F hF
  refine ⟨(integrable_finsetSum _ fun k _ => (hbr k).1).congr hsum, ?_⟩
  calc ∫ c, ∑ z ∈ G.rootSet s (u * c), F z
      = ∫ c, ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k (u * c)) := integral_congr_ae hsum.symm
    _ = ∑ k ∈ Finset.range s, ∫ c, F (NthRootMeasurability.R s k (u * c)) :=
        integral_finsetSum _ fun k _ => (hbr k).1
    _ = ∑ k ∈ Finset.range s, ∫ z in NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z :=
        Finset.sum_congr rfl fun k _ => (hbr k).2
    _ = ∫ z in ⋃ k ∈ Finset.range s, NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z :=
        (integral_biUnion_finset _ (fun k _ => Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A s k)
          (Formalism.FourierDecayAlt.P.NthRootMeasurability.A_disjoint s hs) (fun k _ => hF.integrableOn)).symm
    _ = ∫ z in ({0}ᶜ : Set ℂ), ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
        rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.A_union s hs]
    _ = ∫ z, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
        rw [MeasureTheory.restrict_compl_singleton]

end change

section asym

def lamR (s : ℕ) (σ x : ℂ) : ℂ := (x / (x + σ)) ^ (s - 1)

def rhoR (s : ℕ) (σ x : ℂ) : ℂ := lamR s σ x ^ ((s : ℂ)⁻¹)

theorem eventually_ne_zero_add (σ : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ 0 ∧ x + σ ≠ 0 := by
  have h1 : ∀ᶠ x in cocompact ℂ, x ≠ 0 := (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have h2 : ∀ᶠ x in cocompact ℂ, x ≠ -σ := (isCompact_singleton (x := -σ)).compl_mem_cocompact
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, fun h => hx2 (eq_neg_of_add_eq_zero_left h)⟩

theorem tendsto_eps (σ : ℂ) : Tendsto (fun x : ℂ => σ / (x + σ)) (cocompact ℂ) (𝓝 0) := by
  have h : Tendsto (fun x : ℂ => x + σ) (cocompact ℂ) (cocompact ℂ) :=
    (Homeomorph.addRight σ).map_cocompact.le
  have hinv : Tendsto Inv.inv (cocompact ℂ) (𝓝 (0 : ℂ)) :=
    Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_cobounded
  have h2 := (hinv.comp h).const_mul σ
  simpa [div_eq_mul_inv] using h2

theorem rhoR_eq_eventually (s : ℕ) (σ : ℂ) :
    ∀ᶠ x in cocompact ℂ, rhoR s σ x = (1 - σ / (x + σ)) ^ (((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹) := by
  have h1 : Tendsto (fun x : ℂ => 1 - σ / (x + σ)) (cocompact ℂ) (𝓝 1) := by
    simpa using (Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ).const_sub 1
  have hlog : Tendsto (fun x : ℂ => Complex.log (1 - σ / (x + σ))) (cocompact ℂ) (𝓝 0) := by
    have h2 := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
    simpa [Function.comp_def] using h2
  have hpos : 0 < Real.pi / ((s : ℝ) + 1) := by positivity
  have hsmall : ∀ᶠ x in cocompact ℂ, Complex.log (1 - σ / (x + σ)) ∈ Metric.ball (0 : ℂ) (Real.pi / ((s : ℝ) + 1)) :=
    hlog (Metric.ball_mem_nhds 0 hpos)
  filter_upwards [Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ, hsmall] with x hx hlx
  rw [Metric.mem_ball, dist_zero_right] at hlx

  have hb : ‖Complex.log (1 - σ / (x + σ)) * ((s - 1 : ℕ) : ℂ)‖ < Real.pi := by
    rw [norm_mul, Complex.norm_natCast]
    have hs1 : ((s - 1 : ℕ) : ℝ) ≤ (s : ℝ) + 1 := by
      have : ((s - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
      linarith
    calc ‖Complex.log (1 - σ / (x + σ))‖ * ((s - 1 : ℕ) : ℝ)
        ≤ ‖Complex.log (1 - σ / (x + σ))‖ * ((s : ℝ) + 1) := mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)
      _ < Real.pi / ((s : ℝ) + 1) * ((s : ℝ) + 1) := mul_lt_mul_of_pos_right hlx (by positivity)
      _ = Real.pi := by field_simp
  have him := Complex.abs_im_le_norm (Complex.log (1 - σ / (x + σ)) * ((s - 1 : ℕ) : ℂ))
  have hw : x / (x + σ) = 1 - σ / (x + σ) := by
    field_simp [hx.2]
    ring
  unfold Formalism.FourierDecayAlt.P.PBK.rhoR Formalism.FourierDecayAlt.P.PBK.lamR
  have hlt := abs_lt.mp (lt_of_le_of_lt him hb)
  rw [hw, ← Complex.cpow_natCast, ← Complex.cpow_mul _ hlt.1 hlt.2.le]

theorem tendsto_rhoR (s : ℕ) (σ : ℂ) : Tendsto (rhoR s σ) (cocompact ℂ) (𝓝 1) := by
  have h1 : Tendsto (fun x : ℂ => 1 - σ / (x + σ)) (cocompact ℂ) (𝓝 1) := by
    simpa using (Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ).const_sub 1
  have h2 : Tendsto (fun x : ℂ => (1 - σ / (x + σ)) ^ (((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹)) (cocompact ℂ) (𝓝 1) := by
    have h3 := (continuousAt_cpow_const (b := ((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹)
      (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
    simpa [Function.comp_def] using h3
  exact h2.congr' ((Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s σ).mono fun x hx => hx.symm)

theorem tendsto_shift (s : ℕ) (hs : 1 ≤ s) (σ : ℂ) :
    Tendsto (fun x => (s : ℂ) * (rhoR s σ x * (x + σ) - x)) (cocompact ℂ) (𝓝 σ) := by
  set a : ℂ := ((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹ with ha
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hsa : (s : ℂ) * (1 - a) = 1 := by
    rw [ha, Nat.cast_sub hs]
    field_simp
    ring
  rcases eq_or_ne σ 0 with rfl | hσ
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s 0] with x hx
    rw [hx]
    simp
  ·
    have hφ : HasDerivAt (fun e : ℂ => (1 - e) ^ a) (-a) 0 := by
      have h1 : HasDerivAt (fun e : ℂ => 1 - e) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
      have h2 := h1.cpow_const (c := a) (by simp)
      simpa using h2
    have hslope := hasDerivAt_iff_tendsto_slope.mp hφ
    have hε : Tendsto (fun x : ℂ => σ / (x + σ)) (cocompact ℂ) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ, ?_⟩
      filter_upwards [Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ] with x hx
      exact div_ne_zero hσ hx.2
    have hlim := (((hslope.comp hε).const_mul σ).add_const σ).const_mul (s : ℂ)
    have hval : (s : ℂ) * (σ * -a + σ) = σ := by linear_combination σ * hsa
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s σ, Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ] with x hx hx2
    rw [hx, ← ha]
    simp only [Function.comp_apply, slope_def_field, sub_zero, Complex.one_cpow]
    generalize (1 - σ / (x + σ)) ^ a = φv
    field_simp [hx2.2]
    ring

theorem tendsto_shift_ne (s : ℕ) (hs : 1 ≤ s) (σ ζ : ℂ) (hζ : ζ ≠ 1) :
    Tendsto (fun x => ζ * rhoR s σ x * (x + σ) - x) (cocompact ℂ) (cocompact ℂ) := by
  have hρ := Formalism.FourierDecayAlt.P.PBK.tendsto_rhoR s σ
  have hζ1 : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hA : ∀ᶠ x in cocompact ℂ, ‖ζ - 1‖ / 2 < ‖ζ * rhoR s σ x - 1‖ := by
    have h2 : Tendsto (fun x => ‖ζ * rhoR s σ x - 1‖) (cocompact ℂ) (𝓝 ‖ζ * 1 - 1‖) :=
      ((hρ.const_mul ζ).sub_const 1).norm
    rw [mul_one] at h2
    exact h2.eventually (lt_mem_nhds (by linarith))
  have hB : ∀ᶠ x in cocompact ℂ, ‖ζ * rhoR s σ x * σ‖ < ‖ζ * σ‖ + 1 := by
    have h2 : Tendsto (fun x => ‖ζ * rhoR s σ x * σ‖) (cocompact ℂ) (𝓝 ‖ζ * 1 * σ‖) :=
      ((hρ.const_mul ζ).mul_const σ).norm
    rw [mul_one] at h2
    exact h2.eventually (gt_mem_nhds (by linarith))
  have hc : comap norm atTop = cocompact ℂ := by rw [comap_norm_atTop, Metric.cobounded_eq_cocompact]
  refine (tendsto_comap_iff.mpr ?_).mono_right hc.le
  have hlow : Tendsto (fun x : ℂ => ‖ζ - 1‖ / 2 * ‖x‖ + -(‖ζ * σ‖ + 1)) (cocompact ℂ) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_norm_cocompact_atTop.const_mul_atTop (by linarith))
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [hA, hB] with x hxA hxB

  have heq : ζ * rhoR s σ x * (x + σ) - x = (ζ * rhoR s σ x - 1) * x + ζ * rhoR s σ x * σ := by ring
  have htri := norm_add_le ((ζ * rhoR s σ x - 1) * x + ζ * rhoR s σ x * σ) (-(ζ * rhoR s σ x * σ))
  rw [add_neg_cancel_right, norm_neg, norm_mul] at htri
  have hmul : ‖ζ - 1‖ / 2 * ‖x‖ ≤ ‖ζ * rhoR s σ x - 1‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right hxA.le (norm_nonneg _)
  simp only [Function.comp_apply, heq]
  linarith

end asym

end

end Formalism.FourierDecayAlt.P.PBK
