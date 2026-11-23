import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffCutoffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterIntegralSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveQuadraticUniformLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalInverseFstProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnFderivDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfVariablesInjectiveIndicatorStatement
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff

namespace GlobalTheory

theorem contDiffOn_mean_along_family : ∀ (d : ℕ) (U : Set (Fin d → ℂ)) (N : Set ((Fin d → ℂ) × (Fin d → ℂ))) (G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ) (q : (Fin d → ℂ) → (Fin d → ℂ) → ℝ) (z₀ : Fin d → ℂ), IsOpen U → z₀ ∈ U → IsOpen N → (z₀, 0) ∈ N → ContDiffOn ℝ ∞ G N → G (z₀, 0) = z₀ → HasFDerivAt (fun ξ => G (z₀, ξ)) (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 → ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => q p.1 p.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ (t : ℝ) ξ, q z (t • ξ) = t ^ 2 * q z ξ) → (∀ z ∈ U, ∀ ξ, ξ ≠ 0 → 0 < q z ξ) → ∃ δ : ℝ, 0 < δ ∧ ∃ U' : Set (Fin d → ℂ), IsOpen U' ∧ z₀ ∈ U' ∧ U' ⊆ U ∧ (∀ z ∈ U', ∀ t : ℝ, 0 < t → t < δ → ∀ ξ, q z ξ < 1 → (z, t • ξ) ∈ N) ∧ ∀ ψ : (Fin d → ℂ) → ℝ, MeasureTheory.LocallyIntegrableOn ψ U MeasureTheory.volume → ∀ t : ℝ, 0 < t → t < δ → ContDiffOn ℝ ∞ (fun z => GlobalTheory.ChernReg.mean (q z) fun ξ => ψ (G (z, t • ξ))) U' := by
  intro d U N G q z₀ hU hz₀ hN hz₀N hG hG0 hGd hq hhom hpos
  set N₁ := N ∩ G ⁻¹' U with hN₁
  have hN₁o : IsOpen N₁ := hG.continuousOn.isOpen_inter_preimage hN hU
  have hz₀N₁ : (z₀, 0) ∈ N₁ := ⟨hz₀N, by simp [hG0, hz₀]⟩
  have hG₁ : ContDiffOn ℝ ∞ G N₁ := hG.mono inter_subset_left
  obtain ⟨e, he0, heN, heq, hesymm, hdet⟩ := GlobalTheory.T.exists_local_inverse_fst_prod d N₁ G z₀ hN₁o hz₀N₁ hG₁ hGd
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_source _ he0
  obtain ⟨ε', hε', hballU⟩ := Metric.isOpen_iff.1 hU _ hz₀
  set ρ := min ε ε' / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by have := min_le_left ε ε'; linarith
  have hρε' : ρ < ε' := by have := min_le_right ε ε'; linarith
  have hsrc : ∀ z ∈ closedBall z₀ ρ, ∀ η ∈ closedBall (0 : Fin d → ℂ) ρ, (z, η) ∈ e.source := by
    intro z hz η hη
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.1 hz).trans_lt hρε, (mem_closedBall.1 hη).trans_lt hρε⟩
  have hBU : closedBall z₀ ρ ⊆ U := fun z hz => hballU ((mem_closedBall.1 hz).trans_lt hρε')
  obtain ⟨m, hm, hmq⟩ := GlobalTheory.T.positive_quadratic_uniform_lower_bound d U (closedBall z₀ ρ) q (isCompact_closedBall _ _) hBU hq.continuousOn hhom hpos
  have hkey : ∀ z ∈ closedBall z₀ ρ, ∀ t : ℝ, 0 < t → t < ρ * √m → ∀ η, q z (t⁻¹ • η) < 1 → ‖η‖ < ρ := by
    intro z hz t ht htδ η hη
    have h1 := hmq z hz (t⁻¹ • η)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), mul_pow] at h1
    have h2 : t ^ 2 < ρ ^ 2 * m := by
      have := pow_lt_pow_left₀ htδ ht.le two_ne_zero
      rwa [mul_pow, Real.sq_sqrt hm.le] at this
    by_contra hc
    push_neg at hc
    have h3 : t ^ 2 * t⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]
    have h4 : t ^ 2 * t⁻¹ ^ 2 < ρ ^ 2 * m * t⁻¹ ^ 2 := mul_lt_mul_of_pos_right h2 (by positivity)
    have h5 : m * (t⁻¹ ^ 2 * ρ ^ 2) ≤ m * (t⁻¹ ^ 2 * ‖η‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hc 2) (sq_nonneg _)) hm.le
    linarith
  refine ⟨ρ * √m, by positivity, ball z₀ ρ, isOpen_ball, mem_ball_self hρ, ball_subset_closedBall.trans hBU, ?_, ?_⟩
  · intro z hz t ht htδ ξ hξ
    have h := hkey z (ball_subset_closedBall hz) t ht htδ (t • ξ) (by rwa [inv_smul_smul₀ ht.ne'])
    exact (heN (hsrc z (ball_subset_closedBall hz) _ (mem_closedBall_zero_iff.2 h.le))).1
  intro ψ hψ t ht htδ

  have hsymm1 : ∀ p ∈ e.target, (e.symm p).1 = p.1 := by
    intro p hp
    have := heq _ (e.map_target hp)
    rw [e.right_inv hp] at this
    exact (congrArg Prod.fst this).symm
  have hsymm2 : ∀ p ∈ e.target, G (e.symm p) = p.2 := by
    intro p hp
    have := heq _ (e.map_target hp)
    rw [e.right_inv hp] at this
    exact (congrArg Prod.snd this).symm
  set D : (Fin d → ℂ) × (Fin d → ℂ) → ℝ := fun p => (fderiv ℝ (fun ξ => G (p.1, ξ)) p.2).det with hD
  set Kt : (Fin d → ℂ) × (Fin d → ℂ) → ℝ :=
    e.target.indicator (fun p => cutoff (q p.1 (t⁻¹ • (e.symm p).2)) * |D (e.symm p)|⁻¹) with hKt
  set Kc := e '' (closedBall z₀ ρ ×ˢ closedBall (0 : Fin d → ℂ) ρ) with hKc
  have hKcs : closedBall z₀ ρ ×ˢ closedBall (0 : Fin d → ℂ) ρ ⊆ e.source := fun p hp => by
    simpa using hsrc p.1 hp.1 p.2 hp.2
  have hKcc : IsCompact Kc :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image_of_continuousOn (e.continuousOn.mono hKcs)
  have hKct : Kc ⊆ e.target := by rintro _ ⟨p, hp, rfl⟩; exact e.map_source (hKcs hp)

  have hcut : ∀ p ∈ e.target, p.1 ∈ closedBall z₀ ρ → cutoff (q p.1 (t⁻¹ • (e.symm p).2)) ≠ 0 → p ∈ Kc := by
    intro p hp hp1 hne
    have hq1 := cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' hne)
    have h := hkey _ hp1 t ht htδ _ hq1
    refine ⟨e.symm p, ⟨?_, mem_closedBall_zero_iff.2 h.le⟩, e.right_inv hp⟩
    rw [hsymm1 p hp]; exact hp1
  have hvan : ∀ p : (Fin d → ℂ) × (Fin d → ℂ), p.1 ∈ closedBall z₀ ρ → p ∉ Kc → Kt p = 0 := by
    intro p hp1 hpK
    by_cases hpt : p ∈ e.target
    · rw [hKt, indicator_of_mem hpt]
      by_cases hc : cutoff (q p.1 (t⁻¹ • (e.symm p).2)) = 0
      · simp [hc]
      · exact absurd (hcut p hpt hp1 hc) hpK
    · exact indicator_of_notMem hpt _
  have hUb : ball z₀ ρ ⊆ U := ball_subset_closedBall.trans hBU
  have hDc : ContDiffOn ℝ ∞ D N₁ := GlobalTheory.T.contDiffOn_fderiv_det d N₁ G hN₁o hG₁

  have hKsm : ContDiffOn ℝ ∞ Kt (ball z₀ ρ ×ˢ univ) := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    by_cases hpt : p ∈ e.target
    · have hev : Kt =ᶠ[𝓝 p] fun p => cutoff (q p.1 (t⁻¹ • (e.symm p).2)) * |D (e.symm p)|⁻¹ := by
        filter_upwards [e.open_target.mem_nhds hpt] with p' hp'
        rw [hKt, indicator_of_mem hp']
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hs : ContDiffAt ℝ ∞ e.symm p := hesymm.contDiffAt (e.open_target.mem_nhds hpt)
      have hsrcp : e.symm p ∈ e.source := e.map_target hpt
      have hin : ContDiffAt ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => (p.1, t⁻¹ • (e.symm p).2)) p :=
        contDiffAt_fst.prodMk (hs.snd.const_smul t⁻¹)
      have hqa : ContDiffAt ℝ ∞ (fun r : (Fin d → ℂ) × (Fin d → ℂ) => q r.1 r.2) (p.1, t⁻¹ • (e.symm p).2) :=
        hq.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hUb hp.1, mem_univ _⟩)
      have h1 : ContDiffAt ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => cutoff (q p.1 (t⁻¹ • (e.symm p).2))) p := by
        have h0 := hqa.comp p hin
        exact GlobalTheory.T.contDiff_cutoff'.contDiffAt.comp p h0
      have hDa : ContDiffAt ℝ ∞ D (e.symm p) := hDc.contDiffAt (hN₁o.mem_nhds (heN hsrcp))
      have hD0 : D (e.symm p) ≠ 0 := hdet _ hsrcp
      have h2 : ContDiffAt ℝ ∞ (fun p => |D (e.symm p)|) p := by
        have h0 := (contDiffAt_abs (n := ⊤) hD0).comp p (hDa.comp p hs)
        exact h0
      exact h1.mul (h2.inv (abs_ne_zero.2 hD0))
    · have hpK : p ∉ Kc := fun h => hpt (hKct h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hKcc.isClosed.isOpen_compl.mem_nhds hpK, (isOpen_ball.prod isOpen_univ).mem_nhds hp]
        with p' hp' hp''
      exact hvan p' (ball_subset_closedBall hp''.1) hp'

  set C := Prod.snd '' Kc with hC
  have hCc : IsCompact C := hKcc.image continuous_snd
  have hCU : C ⊆ U := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [heq p (hKcs hp)]
    exact (heN (hKcs hp)).2
  have hnumsm : ContDiffOn ℝ ∞ (fun z => ∫ w, ψ w * Kt (z, w)) (ball z₀ ρ) :=
    GlobalTheory.T.parameter_integral_smooth d (ball z₀ ρ) C Kt ψ isOpen_ball hCc
      (fun z hz w hw => hvan (z, w) (ball_subset_closedBall hz) fun h => hw ⟨_, h, rfl⟩)
      (hψ.integrableOn_compact_subset hCU hCc) hKsm

  have hnum : ∀ z ∈ ball z₀ ρ, ∫ ξ, ψ (G (z, t • ξ)) * cutoff (q z ξ) =
      |(t ^ Module.finrank ℝ (Fin d → ℂ))⁻¹| * ∫ w, ψ w * Kt (z, w) := by
    intro z hz
    have hzc := ball_subset_closedBall hz
    have hsb : ∀ η ∈ ball (0 : Fin d → ℂ) ρ, (z, η) ∈ e.source := fun η hη =>
      hsrc z hzc η (ball_subset_closedBall hη)
    have e1 : ∫ ξ, ψ (G (z, t • ξ)) * cutoff (q z ξ) =
        ∫ ξ, (fun η => ψ (G (z, η)) * cutoff (q z (t⁻¹ • η))) (t • ξ) := by
      simp only [inv_smul_smul₀ ht.ne']
    rw [e1, Measure.integral_comp_smul volume (fun η => ψ (G (z, η)) * cutoff (q z (t⁻¹ • η))) t, smul_eq_mul]
    congr 1
    refine GlobalTheory.T.change_of_variables_injective_indicator d (fun η => G (z, η)) (fun w => (e.symm (z, w)).2) (fun η => fderiv ℝ (fun ξ => G (z, ξ)) η)
      (ball 0 ρ) (fun η => cutoff (q z (t⁻¹ • η))) ψ (fun w => Kt (z, w)) measurableSet_ball ?_ ?_ ?_ ?_ ?_ ?_
    · intro η hη
      have hd : DifferentiableAt ℝ G (z, η) :=
        (hG₁.differentiableOn (by simp)).differentiableAt (hN₁o.mem_nhds (heN (hsb η hη)))
      have h0 := hd.comp η ((differentiableAt_const z).prodMk differentiableAt_id)
      exact h0.hasFDerivAt.hasFDerivWithinAt
    · intro η₁ h₁ η₂ h₂ h
      have := e.injOn (hsb η₁ h₁) (hsb η₂ h₂) (by rw [heq _ (hsb η₁ h₁), heq _ (hsb η₂ h₂)]; exact congrArg _ h)
      exact congrArg Prod.snd this
    · intro η hη
      have := e.left_inv (hsb η hη)
      rw [heq _ (hsb η hη)] at this
      simp only [this]
    · intro η hη
      exact hdet _ (hsb η hη)
    · intro η hη
      by_contra hne
      exact hη (mem_ball_zero_iff.2 (hkey z hzc t ht htδ η (cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' hne))))
    · funext w
      by_cases hw : w ∈ (fun η => G (z, η)) '' ball 0 ρ
      · obtain ⟨η, hη, rfl⟩ := hw
        have hl := e.left_inv (hsb η hη)
        have ht' := e.map_source (hsb η hη)
        rw [heq _ (hsb η hη)] at hl ht'
        rw [indicator_of_mem (mem_image_of_mem _ hη), hKt, indicator_of_mem ht']
        simp only [hl, hD]
      · rw [indicator_of_notMem hw]
        by_cases hpt : (z, w) ∈ e.target
        · by_contra hne
          rw [hKt, indicator_of_mem hpt] at hne
          have hc : cutoff (q z (t⁻¹ • (e.symm (z, w)).2)) ≠ 0 := fun h => hne (by simp [h])
          have hb := hkey z hzc t ht htδ _ (cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' hc))
          have hp1 := hsymm1 _ hpt
          have hp2 := hsymm2 _ hpt
          refine hw ⟨(e.symm (z, w)).2, mem_ball_zero_iff.2 hb, ?_⟩
          have hpe : (z, (e.symm (z, w)).2) = e.symm (z, w) := Prod.ext hp1.symm rfl
          simp only
          rw [hpe]
          exact hp2
        · exact indicator_of_notMem hpt _

  have hden : ContDiffOn ℝ ∞ (fun z => ∫ ξ, cutoff (q z ξ)) (ball z₀ ρ) := by
    have h := GlobalTheory.T.parameter_integral_smooth d (ball z₀ ρ) (closedBall 0 (max 1 m⁻¹)) (fun p => cutoff (q p.1 p.2)) (fun _ => 1)
      isOpen_ball (isCompact_closedBall _ _) ?_ (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
      (GlobalTheory.T.contDiff_cutoff'.comp_contDiffOn (hq.mono (prod_mono hUb subset_rfl)))
    · simpa using h
    · intro z hz w hw
      by_contra hne
      have hq1 := cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' hne)
      have h1 := hmq z (ball_subset_closedBall hz) w
      rw [mem_closedBall_zero_iff, not_le, max_lt_iff] at hw
      have h2 : 1 < m * ‖w‖ := by
        have := mul_lt_mul_of_pos_left hw.2 hm
        rwa [mul_inv_cancel₀ hm.ne'] at this
      have h3 : m * ‖w‖ * 1 < m * ‖w‖ * ‖w‖ := mul_lt_mul_of_pos_left hw.1 (by linarith)
      simp only at hq1
      nlinarith
  have hden0 : ∀ z ∈ ball z₀ ρ, (∫ ξ, cutoff (q z ξ)) ≠ 0 := by
    intro z hz
    have hzU := hUb hz
    have hc : Continuous (q z) :=
      hq.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) fun ξ => ⟨hzU, mem_univ _⟩
    exact (mass_pos hc (hhom z hzU) (hpos z hzU)).ne'
  have hfin := ((contDiffOn_const (c := |(t ^ Module.finrank ℝ (Fin d → ℂ))⁻¹|)).mul hnumsm).div hden hden0
  refine hfin.congr fun z hz => ?_
  simp only [mean]
  rw [hnum z hz, Pi.div_apply]

end GlobalTheory
