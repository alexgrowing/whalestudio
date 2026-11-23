import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff Topology

namespace GlobalTheory

theorem isPotential_contDiffAt_compatChart_base {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (x0 : X)
    (z : Fin e → ℂ) (hz : z ∈ ψ.target) (hzx : ψ.symm z ∈ P.U x0) :
    ContDiffAt ℝ ∞ (P.φ x0 ∘ ψ.symm) z := by
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have h2 : ContDiffAt ℝ ∞ (A.chart j ∘ ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x0) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)
  have hmem : (A.chart j ∘ ψ.symm) z ∈
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x0 := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Function.comp_apply, Set.mem_preimage, (A.chart j).left_inv hj]
    exact hzx
  have h1 : ContDiffAt ℝ ∞ (P.φ x0 ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) :=
    (hP.1 x0 j).contDiffAt (hopen.mem_nhds hmem)
  refine (h1.comp z h2).congr_of_eventuallyEq ?_
  have hev : ∀ᶠ y in 𝓝 z, ψ.symm y ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).eventually ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with y hy
  simp only [Function.comp_apply, (A.chart j).left_inv hy]

theorem levi_base_eq_compatChart {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (x0 : X)
    (z : Fin e → ℂ) (hz : z ∈ ψ.target) (hzx : ψ.symm z ∈ P.U x0) (w : Fin e → ℂ) :
    levi (P.φ (ψ.symm z) ∘ ψ.symm) z w = levi (P.φ x0 ∘ ψ.symm) z w := by
  set y := ψ.symm z with hy
  obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ := hP.2 y x0 y ⟨P.mem_U y, hzx⟩
  obtain ⟨j, hj⟩ := A.cover y
  have hcj : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z := (hψ j).2 z ⟨hz, hj⟩
  have hGj : AnalyticAt ℂ (G ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) := by
    apply hG j
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Function.comp_apply, Set.mem_preimage, ← hy, (A.chart j).left_inv hj]
    exact hyW
  have hsrc : ∀ᶠ z' in 𝓝 z, ψ.symm z' ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).eventually ((A.chart j).open_source.mem_nhds hj)
  have hGa : AnalyticAt ℂ (G ∘ ψ.symm) z := by
    refine (hGj.comp hcj).congr ?_
    filter_upwards [hsrc] with z' hz'
    simp only [Function.comp_apply, (A.chart j).left_inv hz']
  have hΩ : ContDiffAt ℝ 2 (P.φ x0 ∘ ψ.symm) z :=
    (isPotential_contDiffAt_compatChart_base A P hP ψ hψ x0 z hz hzx).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hRe : ContDiffAt ℝ 2 (fun z' => ((G ∘ ψ.symm) z').re) z := by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp z
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this
  have hbase : P.φ y ∘ ψ.symm =ᶠ[𝓝 z]
      fun z' => (P.φ x0 ∘ ψ.symm) z' + 1 * ((G ∘ ψ.symm) z').re := by
    have hopen : IsOpen (W ∩ P.U y ∩ P.U x0) := (hWo.inter (P.isOpen_U y)).inter (P.isOpen_U x0)
    have : ∀ᶠ z' in 𝓝 z, ψ.symm z' ∈ W ∩ P.U y ∩ P.U x0 :=
      (ψ.continuousAt_symm hz).preimage_mem_nhds
        (hopen.mem_nhds ⟨⟨hyW, P.mem_U y⟩, hzx⟩)
    filter_upwards [this] with z' hz'
    have := hGeq (ψ.symm z') hz'
    simp only [Function.comp_apply, one_mul]
    linarith
  rw [levi_congr hbase, levi_add_smul 1 hΩ hRe, levi_re_analytic hGa]
  ring

theorem formAt_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hP : IsPotential A P)
    (hψ : IsCompatChart A ψ) :
    ContinuousOn (fun p : (Fin e → ℂ) × (Fin e → ℂ) => formAt ψ P p.1 p.2)
      (ψ.target ×ˢ Set.univ) := by
  rintro ⟨z0, w0⟩ ⟨hz0, -⟩
  set x0 := ψ.symm z0
  set V := ψ.target ∩ ψ.symm ⁻¹' P.U x0 with hV
  have hVo : IsOpen V := ψ.isOpen_inter_preimage_symm (P.isOpen_U x0)
  have hz0V : z0 ∈ V := ⟨hz0, P.mem_U x0⟩
  have hsm : ContDiffOn ℝ 2 (P.φ x0 ∘ ψ.symm) V := fun z hz =>
    ((isPotential_contDiffAt_compatChart_base A P hP ψ hψ x0 z hz.1 hz.2).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
  have hg : ContinuousOn (fun p : (Fin e → ℂ) × (Fin e → ℂ) =>
      2 / Real.pi * levi (P.φ x0 ∘ ψ.symm) p.1 p.2) (V ×ˢ Set.univ) :=
    (continuousOn_levi hVo hsm).const_smul (2 / Real.pi) |>.congr (fun p _ => by simp [smul_eq_mul])
  have hN : V ×ˢ (Set.univ : Set (Fin e → ℂ)) ∈ 𝓝 (z0, w0) :=
    (hVo.prod isOpen_univ).mem_nhds ⟨hz0V, Set.mem_univ _⟩
  have hgA := hg.continuousAt hN
  refine (hgA.congr ?_).continuousWithinAt
  filter_upwards [hN] with p hp
  simp only [formAt]
  rw [levi_base_eq_compatChart A P hP ψ hψ x0 p.1 hp.1.1 hp.1.2 p.2]

end GlobalTheory
