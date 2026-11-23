import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace RatPosPartLocal

variable {n d : ℕ}

theorem isOpen_ne_zero (q : MvPolynomial (Fin n) ℂ) : IsOpen {x : Fin n → ℂ | eval x q ≠ 0} :=
  isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const

theorem continuousOn_ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} :=
  continuousOn_pi.2 fun r => ((MvPolynomial.continuous_eval (p r)).continuousOn).div
    (MvPolynomial.continuous_eval q).continuousOn fun _ hx => hx

theorem ratPosDens_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ RatChart.ratMap p q (s y) = y)
    (hW : IsOpen W)
    (hWs : ∀ x' ∈ zeroSet J ∩ W, eval x' q ≠ 0 ∧ RatChart.ratMap p q x' ∈ U ∧ s (RatChart.ratMap p q x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    RatChart.ratPosDens J p q (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    obtain ⟨hZ, hq, hR⟩ := hsec y hy.1
    have hfib : s y ∈ RatChart.ratFibre J p q y := ⟨hZ, hq, hR⟩
    have hsh : RatChart.IsRatSheetAt J p q (s y) s :=
      ⟨U, hU, by rw [hR]; exact hy.1, hsd, by rw [hR], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ _ => (hWs x' hx').2.2.symm⟩
    have hex : ∃ s', RatChart.IsRatSheetAt J p q (s y) s' := ⟨s, hsh⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dif_pos hex]
    · have hev : hex.choose =ᶠ[𝓝 y] s := by
        obtain ⟨U₁, hU₁, hxU₁, hsd₁, hsx₁, hsec₁, -⟩ := hex.choose_spec
        rw [hR] at hxU₁ hsx₁
        have hcont : ContinuousAt hex.choose y :=
          hsd₁.continuousOn.continuousAt (hU₁.mem_nhds hxU₁)
        have h1 : ∀ᶠ w in 𝓝 y, hex.choose w ∈ W :=
          hcont.preimage_mem_nhds (by rw [hsx₁]; exact hW.mem_nhds (hEW hy.2))
        filter_upwards [h1, hU₁.mem_nhds hxU₁] with w hwW hwU₁
        have h := (hWs _ ⟨(hsec₁ w hwU₁).1, hwW⟩).2.2
        rw [(hsec₁ w hwU₁).2.2] at h
        exact h.symm
      dsimp only
      rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => hev.fun_comp (φ k),
        Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2.2
          rw [hx.2.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨-, h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl

end RatPosPartLocal

theorem RatPosPartLocal.proof : RatPosPartLocal.Statement := by
  rintro n d J A p q f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩
    ⟨s', U', hU', hxU', hsd', hsx', hsec', V', hV', hVs'⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  set Q := {z : Fin n → ℂ | eval z q ≠ 0} with hQdef
  have hD' : IsOpen (Q ∩ RatChart.ratMap p q ⁻¹' U') :=
    (RatPosPartLocal.continuousOn_ratMap p q).isOpen_inter_preimage (RatPosPartLocal.isOpen_ne_zero q) hU'
  set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (Q ∩ RatChart.ratMap p q ⁻¹' U'))
    with hWdef
  have hW : IsOpen W :=
    (isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter hD')
  have hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x' :=
    by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  have hWs' : ∀ x' ∈ zeroSet J ∩ W,
      eval x' q ≠ 0 ∧ RatChart.ratMap p q x' ∈ U' ∧ s' (RatChart.ratMap p q x') = x' :=
    by
      rintro x' ⟨hZ, -, ⟨hV1, hq1, hU1⟩⟩
      exact ⟨hq1, hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hq1 hU1).symm⟩
  have hxq : eval x q ≠ 0 := by
    have h := (hsec' _ hxU').2.1
    rwa [hsx'] at h
  refine ⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxq, hxU'⟩⟩,
    fun E _ hEW => ?_⟩
  simp_rw [PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW,
    RatPosPartLocal.ratPosDens_eq hU' hsd' hsec' hW hWs' hEW]

  set O' := U' ∩ s' ⁻¹' W with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hU' hW
  have hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z := fun z hz => hWs _ ⟨(hsec' z hz.1).1, hz.2⟩
  have hτd : DifferentiableOn ℂ τ O' := by
    have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
    exact ((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    rw [← (hsec' z₁ h₁.1).2.2, ← (hsec' z₂ h₂.1).2.2, h']
  have hsan : AnalyticOnNhd ℂ s U := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ U ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        have hZ : s y ∈ zeroSet J ∩ W := ⟨(hsec y hyE.1).2, hEW hyE.2⟩
        refine ⟨RatChart.ratMap p q (s y), ⟨(hWs' _ hZ).2.1, ?_⟩, ?_⟩
        · show s' (RatChart.ratMap p q (s y)) ∈ W
          rw [(hWs' _ hZ).2.2]
          exact hZ.2
        · show A *ᵥ s' (RatChart.ratMap p q (s y)) = y
          rw [(hWs' _ hZ).2.2, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator
          (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        by_cases hzE : s' z ∈ E
        · have hm : τ z ∈ U ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]
          have h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z :=
            IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ k (s' w) = φ k (s (τ w))
              rw [(hτU w hw).2]
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            refine ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).1)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          rw [h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (fun hm => hzE (by
              have := hm.2
              rw [Set.mem_preimage, (hτU z hz).2] at this
              exact this)),
            Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ U' ∩ s' ⁻¹' E := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW hzE.2⟩

end

end GroundTheory.Heights₂.Heights
