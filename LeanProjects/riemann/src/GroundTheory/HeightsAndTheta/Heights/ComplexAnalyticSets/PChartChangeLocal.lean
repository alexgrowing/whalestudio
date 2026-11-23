import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ChartChangeLocalOnZero.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ)) (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ)
    (f f' : (Fin n → ℂ) → ℝ) (φ φ' : Fin d → (Fin n → ℂ) → ℝ) (c : Fin d → ℝ)
    (g : Fin d → (Fin n → ℂ) → ℂ) (x' : Fin n → ℂ),
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
    Measurable f → Measurable f' → (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, f' x = f (Φ x)) →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → (∀ k, SmoothNear (zeroSet J') (φ' k)) →
    (∀ k, DifferentiableOn ℂ (g k) U') → (∀ k, ∀ x ∈ U', g k x ≠ 0) →
    (∀ k, ∀ x ∈ U', φ' k x = φ k (Φ x) + c k * Real.log ‖g k x‖) →
    x' ∈ zeroSet J' → linEval u' x' ≠ 0 → (∃ s', IsSheetAt J' A' x' s') →
    (∃ s, IsSheetAt J A (Φ x') s) →
      ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ x' ∈ W' ∧
        ∀ E' : Set (Fin n → ℂ), MeasurableSet E' → E' ⊆ W' →
          ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' (E'.indicator f') φ' y) =
            ∫⁻ y, ENNReal.ofReal (chartPosDens J A ((Φ '' (E' ∩ zeroSet J')).indicator f) φ y)

namespace ChartChangeLocalOnZero

variable {D : ℕ}

theorem hessC_add_smul_log_norm (ψ : (Fin D → ℂ) → ℝ) (h : (Fin D → ℂ) → ℂ) (c : ℝ) (z : Fin D → ℂ)
    (hψ : ContDiffAt ℝ 2 ψ z) (hh : AnalyticAt ℂ h z) (hz : h z ≠ 0) :
    ReciprocityTheory.AnForm.hessC (fun w => ψ w + c * Real.log ‖h w‖) z = ReciprocityTheory.AnForm.hessC ψ z := by
  obtain ⟨G, hG, heq⟩ := ReciprocityTheory.AnForm.A.exists_re_analytic_eq_log_norm h z hh hz
  have h1 : (fun w => ψ w + c * Real.log ‖h w‖) =ᶠ[𝓝 z] fun w => ψ w + ((c : ℂ) * G w).re :=
    heq.mono fun w hw => by
      simp only at hw
      show ψ w + c * Real.log ‖h w‖ = ψ w + ((c : ℂ) * G w).re
      rw [hw, Complex.re_ofReal_mul]
  rw [ReciprocityTheory.AnForm.A.hessC_congr' h1]
  exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic ψ (fun w => (c : ℂ) * G w) z hψ
    (analyticAt_const.mul hG)

end ChartChangeLocalOnZero

theorem ChartChangeLocalOnZero.proof : ChartChangeLocalOnZero.Statement := by
  rintro n d J J' A A' u u' U U' Φ Ψ f f' φ φ' c g x' hU hU' hZU hZU' hΦd hΨd hΦm hΨm hΨΦ hΦΨ hf hf'
    hff' hφ hφ' hgd hg0 hφφ' hx' hux' ⟨s', V1', hV1', hxV1', hsd', -, hsec', N', hN', hNs'⟩
    ⟨s, V1, hV1, hxV1, hsd, -, hsec, N, hN, hNs⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hAc' : Continuous fun z : Fin n → ℂ => A' *ᵥ z := by fun_prop
  have hlin : Continuous (linEval u') := by unfold linEval; fun_prop
  set W := interior N ∩ (fun z => A *ᵥ z) ⁻¹' V1 with hWdef
  have hW : IsOpen W := isOpen_interior.inter (hV1.preimage hAc)
  set W' := ((interior N' ∩ (fun z => A' *ᵥ z) ⁻¹' V1') ∩ {x | linEval u' x ≠ 0}) ∩ (U' ∩ Φ ⁻¹' W)
    with hW'def
  have hW' : IsOpen W' :=
    ((isOpen_interior.inter (hV1'.preimage hAc')).inter (isOpen_ne_fun hlin continuous_const)).inter
      (hΦd.continuousOn.isOpen_inter_preimage hU' hW)
  have hZ'U' : ∀ p ∈ zeroSet J' ∩ W', p ∈ zeroSet J' \ {x | linEval u' x = 0} :=
    fun p hp => ⟨hp.1, hp.2.1.2⟩
  have hWs' : ∀ p ∈ zeroSet J' ∩ W', A' *ᵥ p ∈ V1' ∧ s' (A' *ᵥ p) = p := by
    rintro p ⟨hZ, ⟨⟨hN1, hV⟩, -⟩, -⟩
    exact ⟨hV, (hNs' p ⟨hZ, interior_subset hN1⟩ hV).symm⟩
  have hWs : ∀ p ∈ zeroSet J ∩ W, A *ᵥ p ∈ V1 ∧ s (A *ᵥ p) = p := by
    rintro p ⟨hZ, hN1, hV⟩
    exact ⟨hV, (hNs p ⟨hZ, interior_subset hN1⟩ hV).symm⟩
  have hΦW : ∀ p ∈ zeroSet J' ∩ W', Φ p ∈ zeroSet J ∩ W := fun p hp =>
    ⟨(hΦm (hZ'U' p hp)).1, hp.2.2.2⟩
  have hxW' : x' ∈ W' :=
    ⟨⟨⟨mem_interior_iff_mem_nhds.2 hN', hxV1'⟩, hux'⟩, hZU' ⟨hx', hux'⟩,
      ⟨mem_interior_iff_mem_nhds.2 hN, hxV1⟩⟩
  refine ⟨W', hW', hxW', fun E' _ hEW' => ?_⟩
  set E := Φ '' (E' ∩ zeroSet J') with hEdef
  have hEW : E ⊆ W := by
    rintro _ ⟨p, ⟨hpE, -⟩, rfl⟩
    exact (hEW' hpE).2.2
  simp_rw [PosPartLocal.chartPosDens_eq hV1' hsd' hsec' hW' hWs' hEW',
    PosPartLocal.chartPosDens_eq hV1 hsd hsec hW hWs hEW]

  set O' := V1' ∩ s' ⁻¹' W' with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ Φ (s' z) with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hV1' hW'
  have hs'Z : ∀ z ∈ O', s' z ∈ zeroSet J' ∩ W' := fun z hz => ⟨(hsec' z hz.1).2, hz.2⟩
  have hτU : ∀ z ∈ O', τ z ∈ V1 ∧ s (τ z) = Φ (s' z) := fun z hz => hWs _ (hΦW _ (hs'Z z hz))
  have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
  have hτd : DifferentiableOn ℂ τ O' := by
    have hΦs : DifferentiableOn ℂ (fun z => Φ (s' z)) O' :=
      hΦd.comp hs'O fun z hz => (hs'Z z hz).2.2.1
    exact (Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hΦs
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hΦinj : ∀ p ∈ zeroSet J' ∩ W', ∀ q ∈ zeroSet J' ∩ W', Φ p = Φ q → p = q := fun p hp q hq h => by
    rw [← hΨΦ p (hZ'U' p hp), ← hΨΦ q (hZ'U' q hq), h]
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    have h'' := hΦinj _ (hs'Z z₁ h₁) _ (hs'Z z₂ h₂) h'
    rw [← (hsec' z₁ h₁.1).1, ← (hsec' z₂ h₂.1).1, h'']
  have hsan : AnalyticOnNhd ℂ s V1 := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV1 hsd
  symm
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((V1 ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ V1 ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        obtain ⟨p, ⟨hpE, hpZ⟩, hp⟩ := hyE.2
        have hpW : p ∈ zeroSet J' ∩ W' := ⟨hpZ, hEW' hpE⟩
        refine ⟨A' *ᵥ p, ⟨(hWs' p hpW).1, ?_⟩, ?_⟩
        · show s' (A' *ᵥ p) ∈ W'
          rw [(hWs' p hpW).2]
          exact hpW.2
        · show A *ᵥ Φ (s' (A' *ᵥ p)) = y
          rw [(hWs' p hpW).2, hp, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((V1 ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((V1' ∩ s' ⁻¹' E').indicator
          (fun y => max (f' (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ' k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        have hzW := hs'Z z hz
        by_cases hzE : s' z ∈ E'
        · have hm : τ z ∈ V1 ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact ⟨s' z, ⟨hzE, hzW.1⟩, rfl⟩⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ V1' ∩ s' ⁻¹' E' from ⟨hz.1, hzE⟩)]
          have hC2 : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (τ z) := fun k => by
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hΦW _ hzW).1)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          have h1 : ∀ k, ReciprocityTheory.AnForm.hessC (φ' k ∘ s') z =
              ReciprocityTheory.AnForm.hessC ((φ k ∘ s) ∘ τ) z := fun k => by
            have hgs : AnalyticAt ℂ (fun w => g k (s' w)) z :=
              ReciprocityTheory.AnForm.Osgood.osgood d O' _ hO'
                ((hgd k).comp hs'O fun w hw => (hs'Z w hw).2.2.1) z hz
            have heq : φ' k ∘ s' =ᶠ[𝓝 z]
                fun w => ((φ k ∘ s) ∘ τ) w + c k * Real.log ‖g k (s' w)‖ := by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ' k (s' w) = φ k (s (τ w)) + c k * Real.log ‖g k (s' w)‖
              rw [(hτU w hw).2, hφφ' k (s' w) (hs'Z w hw).2.2.1]
            rw [ReciprocityTheory.AnForm.A.hessC_congr' heq]
            exact ChartChangeLocalOnZero.hessC_add_smul_log_norm _ _ _ z
              ((hC2 k).comp z ((hτan z hz).contDiffAt.restrict_scalars ℝ)) hgs
              (hg0 k _ (hs'Z z hz).2.2.1)
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => φ' k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            rw [← ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) hC2]
            simp only [ReciprocityTheory.AnForm.maDens, h1]
          have h3 : f' (s' z) = f (s (τ z)) := by rw [(hτU z hz).2, hff' _ (hZ'U' _ hzW)]
          rw [h2, h3, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · have hnm : τ z ∉ V1 ∩ s ⁻¹' E := by
            rintro ⟨-, hm⟩
            rw [Set.mem_preimage, (hτU z hz).2] at hm
            obtain ⟨p, ⟨hpE, hpZ⟩, hp⟩ := hm
            exact hzE (by rw [← hΦinj _ ⟨hpZ, hEW' hpE⟩ _ hzW hp]; exact hpE)
          rw [Set.indicator_of_notMem hnm,
            Set.indicator_of_notMem (show z ∉ V1' ∩ s' ⁻¹' E' from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ V1' ∩ s' ⁻¹' E' := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW' hzE.2⟩

end

end GroundTheory.Heights₂.Heights
