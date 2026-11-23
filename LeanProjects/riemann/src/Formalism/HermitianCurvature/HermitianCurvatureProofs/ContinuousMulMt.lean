import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.FrameInvMulVecNegativeVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

def mulMt {k r : ℕ} (s x : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r := fun i j => (Matrix.of s * Matrix.of x) i j

theorem continuous_mulMt {k r : ℕ} :
    Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => mulMt q.1 q.2) := by
  unfold mulMt
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurable_mulMt {k r : ℕ} :
    Measurable (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => mulMt q.1 q.2) := by
  exact continuous_mulMt.measurable

private theorem continuous_mulMt_right_const {k r : ℕ} (x : Formalism.QuantumDeterminants.Mt k r) :
    Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => mulMt s x) := by
  unfold mulMt
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

set_option maxHeartbeats 800000 in

theorem quot_zero_real {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (f : Formalism.QuantumDeterminants.Mt k r → ℝ) (hfm : Measurable f)
    (hfi : Integrable f μG) (hin : ∀ᵐ x ∂νq, ∫ s, f (mulMt s x) ∂μS = 0) : ∫ x, f x ∂μG = 0 := by
  have hmm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => f (mulMt p.2 p.1)) :=
    hfm.comp (measurable_mulMt.comp measurable_swap)
  have hab : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal |f (mulMt p.2 p.1)|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hmm)
  have hG := hab.lintegral_prod_right' (ν := μS)
  have hqa := hq (fun y => ENNReal.ofReal |f y|) (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hfm))
  have hfin : ∫⁻ x, ∫⁻ s, ENNReal.ofReal |f (mulMt s x)| ∂μS ∂νq ≠ ⊤ := by
    have h1 : ∫⁻ y, ENNReal.ofReal |f y| ∂μG < ⊤ := hfi.abs.lintegral_lt_top
    rw [hqa] at h1
    exact h1.ne
  have hae := ae_lt_top hG hfin
  have hpos := hq (fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hfm)
  have hneg := hq (fun y => ENNReal.ofReal (-f y)) (ENNReal.measurable_ofReal.comp hfm.neg)
  have heq : ∫⁻ y, ENNReal.ofReal (f y) ∂μG = ∫⁻ y, ENNReal.ofReal (-f y) ∂μG := by
    rw [hpos, hneg]
    refine lintegral_congr_ae ((hae.and hin).mono fun x hx => ?_)
    obtain ⟨hxG, hx0⟩ := hx
    have hxG' : ∫⁻ s, ENNReal.ofReal |f (mulMt s x)| ∂μS < ⊤ := hxG
    have hmeasx : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (mulMt s x)) :=
      hfm.comp (continuous_mulMt_right_const x).measurable
    have hint : Integrable (fun s => f (mulMt s x)) μS := by
      refine ⟨hmeasx.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_norm]
      simpa only [Real.norm_eq_abs] using hxG'
    have hp : ∫⁻ s, ENNReal.ofReal (f (mulMt s x)) ∂μS ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono fun s => ENNReal.ofReal_le_ofReal (le_abs_self _)) hxG').ne
    have hn : ∫⁻ s, ENNReal.ofReal (-f (mulMt s x)) ∂μS ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono fun s => ENNReal.ofReal_le_ofReal (neg_le_abs _)) hxG').ne
    have h2 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
    rw [hx0] at h2
    exact (ENNReal.toReal_eq_toReal_iff' hp hn).mp (sub_eq_zero.mp h2.symm)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi, heq, sub_self]

set_option maxHeartbeats 800000 in

theorem quot_zero {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (F : Formalism.QuantumDeterminants.Mt k r → ℂ) (hFm : Measurable F)
    (hFi : Integrable F μG) (hin : ∀ᵐ x ∂νq, ∫ s, F (mulMt s x) ∂μS = 0) : ∫ x, F x ∂μG = 0 := by
  have hmm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => F (mulMt p.2 p.1)) :=
    hFm.comp (measurable_mulMt.comp measurable_swap)
  have hab : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal ‖F (mulMt p.2 p.1)‖) :=
    ENNReal.measurable_ofReal.comp hmm.norm
  have hG := hab.lintegral_prod_right' (ν := μS)
  have hqa := hq (fun y => ENNReal.ofReal ‖F y‖) (ENNReal.measurable_ofReal.comp hFm.norm)
  have hfin : ∫⁻ x, ∫⁻ s, ENNReal.ofReal ‖F (mulMt s x)‖ ∂μS ∂νq ≠ ⊤ := by
    have h1 : ∫⁻ y, ENNReal.ofReal ‖F y‖ ∂μG < ⊤ := hFi.norm.lintegral_lt_top
    rw [hqa] at h1
    exact h1.ne
  have hae := ae_lt_top hG hfin
  have hint : ∀ᵐ x ∂νq, Integrable (fun s => F (mulMt s x)) μS := by
    refine hae.mono fun x hx => ⟨(hFm.comp (continuous_mulMt_right_const x).measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact hx
  have hre := quot_zero_real hq (fun y => (F y).re) (Complex.measurable_re.comp hFm)
    (Complex.reCLM.integrable_comp hFi) ((hint.and hin).mono fun x hx => by
      have e := Complex.reCLM.integral_comp_comm hx.1
      simp only [Complex.reCLM_apply] at e
      show ∫ s, (F (mulMt s x)).re ∂μS = 0
      rw [e, hx.2, Complex.zero_re])
  have him := quot_zero_real hq (fun y => (F y).im) (Complex.measurable_im.comp hFm)
    (Complex.imCLM.integrable_comp hFi) ((hint.and hin).mono fun x hx => by
      have e := Complex.imCLM.integral_comp_comm hx.1
      simp only [Complex.imCLM_apply] at e
      show ∫ s, (F (mulMt s x)).im ∂μS = 0
      rw [e, hx.2, Complex.zero_im])
  have er := Complex.reCLM.integral_comp_comm hFi
  have ei := Complex.imCLM.integral_comp_comm hFi
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at er ei
  apply Complex.ext
  · rw [Complex.zero_re, ← er]
    exact hre
  · rw [Complex.zero_im, ← ei]
    exact him

section Groups

variable {k r : ℕ}

theorem uwset_eq (z : Fin (2 * r + k + 1) → ℂ) : Formalism.QuantumDeterminants.UWset k r z = PI.UpqRep.UWset k r z := rfl

theorem uh_eq : Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) = PI.UpqRep.UH (PI.UpqRep.Hpk k r) := rfl

private theorem hpk_sq_lemma (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  obtain ⟨s, hs⟩ : ∃ s : Fin (2 * r + k + 1),
      s.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) :=
    ⟨⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single s]
  · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs ⊢ <;> first | omega | norm_num
  · intro l _ hl
    simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff] at hl ⊢
    split_ifs at hs ⊢ <;> first | omega | simp
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem inv_mem_UH_Hpk_and_mul_inv_of_mem {k r : ℕ} {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hH : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    intro h0
    have h3 := congrArg Matrix.det (hpk_sq_lemma k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h3
    exact zero_ne_one h3
  have hdet : IsUnit g.det := by
    have h3 := congrArg Matrix.det hg'
    rw [Matrix.det_mul, Matrix.det_mul] at h3
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h3
    exact hH h3.symm
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have h2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  refine ⟨?_, h1, h2⟩
  show (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = Formalism.QuantumDeterminants.Hpk k r
  calc (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hh : h ∈ Formalism.QuantumDeterminants.UWset k r z) :
    h⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ h * h⁻¹ = 1 ∧ h⁻¹ * h = 1 := by
  obtain ⟨hH, hfix, hz⟩ := hh
  obtain ⟨hi, h1, h2⟩ := inv_mem_UH_Hpk_and_mul_inv_of_mem hH
  have key : ∀ w, h *ᵥ w = w → h⁻¹ *ᵥ w = w := fun w hw => by
    calc h⁻¹ *ᵥ w = h⁻¹ *ᵥ (h *ᵥ w) := by rw [hw]
      _ = w := by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  exact ⟨⟨hi, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩, h1, h2⟩

theorem uh_inv {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  exact inv_mem_UH_Hpk_and_mul_inv_of_mem hg

end Groups

section Pi

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem piW_facts {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    π 1 = 1 ∧ (∀ a ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ b ∈ Formalism.QuantumDeterminants.UWset k r z, π (a * b) = (π a).comp (π b)) ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ w, ‖π h w‖ = ‖w‖) ∧
      (∀ w, ContinuousOn (fun h => π h w) (Formalism.QuantumDeterminants.UWset k r z)) := by
  rw [uwset_eq]
  obtain ⟨g, hg, hρ⟩ := hπ
  obtain ⟨⟨h1, hmul⟩, hunit, hcont⟩ := hρ.2.2.1
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hg.1
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hg.1
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (1 : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) = g * PI.UpqRep.blockW k r 1 * g⁻¹ := by
      rw [PI.HwUniqW.blockW_one, Matrix.mul_one, hgg]
    rw [e]; exact h1
  · intro a ha b hb
    obtain ⟨x, hx, -, rfl⟩ := PI.HwUniqW.UW_eq_conj hT' hg ha
    obtain ⟨y, hy, -, rfl⟩ := PI.HwUniqW.UW_eq_conj hT' hg hb
    have e : g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹) =
        g * PI.UpqRep.blockW k r (x * y) * g⁻¹ := by
      rw [← PI.HwUniqW.blockW_mul]
      calc g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹)
          = g * PI.UpqRep.blockW k r x * (g⁻¹ * g) * PI.UpqRep.blockW k r y * g⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e]; exact hmul x hx y hy
  · intro h hh w
    obtain ⟨x, hx, -, rfl⟩ := PI.HwUniqW.UW_eq_conj hT' hg hh
    exact hunit x hx w
  · intro w
    have hc : Continuous (fun h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => PI.HwUniqW.sub k r (g⁻¹ * h * g)) := by
      have h0 : Continuous (fun h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => g⁻¹ * h * g) :=
        (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      unfold PI.HwUniqW.sub
      exact continuous_pi fun a => continuous_pi fun b =>
        (continuous_apply_apply (PI.HwUniqW.bl k r a) (PI.HwUniqW.bl k r b)).comp h0
    have hmaps : Set.MapsTo (fun h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => PI.HwUniqW.sub k r (g⁻¹ * h * g))
        (PI.UpqRep.UWset k r z) (PI.UpqRep.UJset (PI.UpqRep.allPos k)) := fun h hh =>
      (PI.HwUniqW.fix_block (PI.HwUniqW.conj_UH hg hh) (PI.HwUniqW.conj_fix hT' hg hh)).1
    refine ((hcont w).comp hc.continuousOn hmaps).congr ?_
    intro h hh
    have hb := (PI.HwUniqW.fix_block (PI.HwUniqW.conj_UH hg hh) (PI.HwUniqW.conj_fix hT' hg hh)).2
    show π h w = π (g * PI.UpqRep.blockW k r (PI.HwUniqW.sub k r (g⁻¹ * h * g)) * g⁻¹) w
    rw [← hb]
    congr 2
    calc h = (g * g⁻¹) * h * (g * g⁻¹) := by rw [hgg, Matrix.one_mul, Matrix.mul_one]
      _ = g * (g⁻¹ * h * g) * g⁻¹ := by simp only [Matrix.mul_assoc]

theorem piW_unitary {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ w, ‖π h w‖ = ‖w‖ := by
  exact (piW_facts hT hπ).2.2.1

theorem piW_cont {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ∀ w, ContinuousOn (fun h => π h w) (Formalism.QuantumDeterminants.UWset k r z) := by
  exact (piW_facts hT hπ).2.2.2

theorem piW_inner {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hh : h ∈ Formalism.QuantumDeterminants.UWset k r z) (η w : Wp) : ⟪η, π h w⟫_ℂ = ⟪π h⁻¹ η, w⟫_ℂ := by
  obtain ⟨h1, hmul, hnorm, -⟩ := piW_facts hT hπ
  obtain ⟨hi, hhi, -⟩ := uw_inv hh
  have hm := hmul h hh h⁻¹ hi
  rw [hhi, h1] at hm
  have hs : ∀ x, π h (π h⁻¹ x) = x := fun x => by
    have h3 := congrArg (fun T : Wp →L[ℂ] Wp => T x) hm
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h3
    exact h3.symm
  let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π h : Wp →ₗ[ℂ] Wp), norm_map' := hnorm h hh }
  calc ⟪η, π h w⟫_ℂ = ⟪L (π h⁻¹ η), L w⟫_ℂ := by
        show ⟪η, π h w⟫_ℂ = ⟪π h (π h⁻¹ η), π h w⟫_ℂ
        rw [hs]
    _ = ⟪π h⁻¹ η, w⟫_ℂ := L.inner_map_map _ _

end Pi

section Sigma

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem cayley_maps {ε : Fin (2 * r + k + 1) → Bool} {P : Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) :
    Set.MapsTo (fun g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by
  obtain ⟨⟨hPu, hPJ⟩, -⟩ := hP
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  intro g hg
  have hg' : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹) = PI.UpqRep.Jm ε
  calc (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹ := by rw [hPJ, hg']
    _ = (P * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = PI.UpqRep.Jm ε := by rw [hPPi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem sigma_facts {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ v, ‖σ g v‖ = ‖v‖ := by
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨-, -, ⟨⟨h1, -⟩, hnorm, -⟩, -⟩ := hDS
  have hPu : IsUnit P := hP.1.1
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  refine ⟨?_, fun g hg v => ?_⟩
  · simp only [Matrix.mul_one, hPiP] at h1
    exact h1
  · have hmem := cayley_maps hP hg
    have hv := hnorm _ hmem v
    have e : P⁻¹ * (P * g * P⁻¹) * P = g := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]
    simp only [e] at hv
    exact hv

theorem sigma_inner {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (v u : H) :
    ⟪v, σ g u⟫_ℂ = ⟪σ g⁻¹ v, u⟫_ℂ := by
  obtain ⟨P, hP, hDS⟩ := id hσ
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hnorm, -⟩, -⟩ := hDS
  have hPu : IsUnit P := hP.1.1
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  obtain ⟨hgi, hggi, hgig⟩ := uh_inv hg
  have hm1 := cayley_maps hP hg
  have hm2 := cayley_maps hP hgi
  have conj : ∀ x : Formalism.FourierDecayAlt.ThreeDimData.Mx k r, P⁻¹ * (P * x * P⁻¹) * P = x := fun x => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]
  have prod : ∀ x y : Formalism.FourierDecayAlt.ThreeDimData.Mx k r, (P * x * P⁻¹) * (P * y * P⁻¹) = P * (x * y) * P⁻¹ := fun x y => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, hPiP, Matrix.one_mul]
  have hm := hmul _ hm1 _ hm2
  simp only [prod, hggi, conj, Matrix.mul_one, Matrix.one_mul, hPiP, hPPi] at hm h1

  have hsg : ∀ w, σ g (σ g⁻¹ w) = w := fun w => by
    have := congrArg (fun T : H →L[ℂ] H => T w) hm
    simp only [ContinuousLinearMap.comp_apply, h1, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have hn : ∀ w, ‖σ g w‖ = ‖w‖ := fun w => by
    have := hnorm _ hm1 w
    simp only [conj] at this
    exact this
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hn }
  calc ⟪v, σ g u⟫_ℂ = ⟪L (σ g⁻¹ v), L u⟫_ℂ := by
        show ⟪v, σ g u⟫_ℂ = ⟪σ g (σ g⁻¹ v), σ g u⟫_ℂ
        rw [hsg]
    _ = ⟪σ g⁻¹ v, u⟫_ℂ := L.inner_map_map _ _

end Sigma

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
