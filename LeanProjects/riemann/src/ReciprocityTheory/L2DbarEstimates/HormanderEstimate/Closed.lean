import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ClosedCoreOfRegM
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ClosedEval

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

private lemma lintegral_enorm_sq_wvol_eq_wint (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) (ψ : M → ℝ)
    (hψ : Measurable ψ) (u : M → ℂ) :
    ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂(H.wvol n z ψ) = wint n z u ψ := by
  have hdm : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ x)) :=
    (Real.measurable_exp.comp hψ.neg).ennreal_ofReal
  rw [H.wvol, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  unfold wint
  refine lintegral_congr fun x => ?_
  have h2 : ‖u x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖u x‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  simp only [Pi.mul_apply]
  rw [h2, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem needBergmanClosed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : RegMStatement n M) :
    H.NeedBergmanClosed n M := by
  intro z hz ψ hψ
  have hdm : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ x)) :=
    (Real.measurable_exp.comp hψ.measurable.neg).ennreal_ofReal
  have hac : vol n z ≪ H.wvol n z ψ :=
    withDensity_absolutelyContinuous' hdm.aemeasurable
      (ae_of_all _ fun x => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
  have hac' : H.wvol n z ψ ≪ vol n z := withDensity_absolutelyContinuous _ _
  refine IsSeqClosed.isClosed ?_
  intro Fs F hFs hlim
  have hex : ∀ k, ∃ f : M → ℂ, Holo n z f ∧ (Fs k : M → ℂ) =ᵐ[H.wvol n z ψ] f := hFs
  choose fk hfk hFk using hex
  have hF : AEStronglyMeasurable (⇑F) (vol n z) := (Lp.aestronglyMeasurable F).mono_ac hac
  have key : ∀ k, eLpNorm (⇑(Fs k) - ⇑F) 2 (H.wvol n z ψ) =
      wint n z (fun x => fk k x - F x) ψ ^ (1 / (2:ℝ)) := by
    intro k
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    rw [lintegral_congr_ae (g := fun x => ‖fk k x - F x‖ₑ ^ (2:ℝ))
      ((hFk k).mono fun x hx => by simp only [Pi.sub_apply, hx])]
    exact lintegral_enorm_sq_wvol_eq_wint n z ψ hψ.measurable _
  have hT : Tendsto (fun k => wint n z (fun x => fk k x - F x) ψ) atTop (𝓝 0) := by
    have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hlim
    have h2 := ((ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto 0).comp h1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [key k, ← ENNReal.rpow_mul]
    norm_num
  obtain ⟨G, hG, hFG⟩ := closedCore_of_regM n M hReg z hz ψ hψ fk (⇑F) hfk hF hT
  exact ⟨G, hG, hac'.ae_le hFG⟩

theorem holoClosedNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : RegMStatement n M) :
    I.HoloClosedNeed n M := by
  intro X ps F f hps hF hf hT
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hc : Continuous ps := continuous_of_smoothR n X.z hz ps hps
  exact closedCore_of_regM n M hReg X.z hz ps hc F f hF hf.aestronglyMeasurable hT

theorem evalNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMV : C.MVStatement) :
    I.EvalNeed n M := by
  intro X ps x0 hps
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hc : Continuous ps := continuous_of_smoothR n X.z hz ps hps
  obtain ⟨C, -, hC⟩ := evalPt n M hMV X.z hz ps hc x0
  exact ⟨C, hC⟩

end

end ReciprocityTheory.L2DbarEstimates.F
