import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLocDensContOnOpen
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens potSmoothOn hessCGerm maDens_congr_hessC
  maDens_continuousOn)

theorem LocDensContOnOpen.proof : LocDensContOnOpen.Statement := by
  intro D X _ A Yo th u hYo hth hu j y0 hy0
  apply ContinuousAt.continuousWithinAt
  have hu2 : ∀ i, ContDiffOn ℝ 2 (u i ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    fun i => (hu i j).of_le (WithTop.coe_le_coe.2 le_top)
  have hNo : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) :=
    (A.chart j).isOpen_inter_preimage_symm
      (hYo.inter (isOpen_iInter_of_finite fun i => (th i).isOpen_U _))
  have hy0N : y0 ∈ (A.chart j).target ∩
      (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0)) :=
    ⟨hy0.1, hy0.2, Set.mem_iInter.2 fun i => (th i).mem_U _⟩
  have hsm : ∀ i, ContDiffOn ℝ 2 (fun y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) ((A.chart j).target ∩
        (A.chart j).symm ⁻¹' (Yo ∩ ⋂ i, (th i).U ((A.chart j).symm y0))) := fun i =>
    ((potSmoothOn A (th i) (hth i) _ j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i⟩).add
      ((hu2 i).mono fun y hy => ⟨hy.1, hy.2.1⟩)
  have heq : ReciprocityTheory.AnForm.maDens (fun i y' => (th i).φ ((A.chart j).symm y0) ((A.chart j).symm y') +
      u i ((A.chart j).symm y')) =ᶠ[nhds y0] locDens A (fun i => potForm (th i) (u i)) j := by
    filter_upwards [hNo.mem_nhds hy0N] with y hy
    unfold locDens
    apply maDens_congr_hessC
    intro i
    have hp0 : (A.chart j).symm y ∈ (th i).U ((A.chart j).symm y0) := Set.mem_iInter.1 hy.2.2 i
    obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ :=
      (hth i).2 ((A.chart j).symm y) ((A.chart j).symm y0) ((A.chart j).symm y) ⟨(th i).mem_U _, hp0⟩
    have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0))) :=
      (A.chart j).isOpen_inter_preimage_symm
        ((hWo.inter ((th i).isOpen_U _)).inter ((th i).isOpen_U _))
    have hyV : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (W ∩ (th i).U ((A.chart j).symm y) ∩ (th i).U ((A.chart j).symm y0)) :=
      ⟨hy.1, ⟨hyW, (th i).mem_U _⟩, hp0⟩
    have h1 : (fun y' => (potForm (th i) (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
        (fun w => ((th i).φ ((A.chart j).symm y0) ((A.chart j).symm w) + u i ((A.chart j).symm w)) +
          ((G ∘ (A.chart j).symm) w).re) := by
      filter_upwards [hVo.mem_nhds hyV] with w hw
      have := hGeq ((A.chart j).symm w) hw.2
      show (th i).φ _ _ + u i _ = _
      simp only [Function.comp_apply]
      linarith
    exact ((hessCGerm _ _ _ h1).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _
      ((hsm i).contDiffAt (hNo.mem_nhds hy)) (hG j y ⟨hy.1, hyW⟩))).symm
  refine ContinuousAt.congr ?_ heq
  exact (maDens_continuousOn _ _ hNo hsm).continuousAt (hNo.mem_nhds hy0N)

end GroundTheory.Heights₂.Heights.AnalyticLimit
