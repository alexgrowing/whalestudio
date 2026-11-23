import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ChartPsh

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic

variable {D : ℕ} {Y : Type} [TopologicalSpace Y]

theorem sup'_bool (a c : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun b : Bool => if b then a else c) = max a c := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun b _ => by cases b <;> simp
  · exact max_le (by simpa using Finset.le_sup' (fun b : Bool => if b then a else c) (Finset.mem_univ true))
      (by simpa using Finset.le_sup' (fun b : Bool => if b then a else c) (Finset.mem_univ false))

theorem local_form (A : FinHolAtlas D Y) (Θ : LocPot Y) (u : Y → ℝ) (S : Set Y) (x : Y)
    (Φ : OpenPartialHomeomorph Y (Fin D → ℂ)) (hS : IsOpen S) (hΘ : IsPotential A Θ)
    (hu : A.SmoothOn S u) (hN : SumNonnegOn A Θ u S) (hΦ : IsCompatChart A Φ)
    {w₀ : Fin D → ℂ} (hw : w₀ ∈ Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) :
    ContDiffAt ℝ 2 (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) w₀ ∧
      ∀ v, 0 ≤ levi (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) w₀ v := by
  have hyΦ : Φ.symm w₀ ∈ Φ.source := Φ.map_target hw.1
  obtain ⟨j, hj⟩ := A.cover (Φ.symm w₀)
  let F : (Fin D → ℂ) → ℝ := fun z => 2 * Θ.φ x ((A.chart j).symm z) + u ((A.chart j).symm z)
  let τ : (Fin D → ℂ) → (Fin D → ℂ) := A.chart j ∘ Φ.symm
  have hτa : AnalyticAt ℂ τ w₀ := (hΦ j).2 w₀ ⟨hw.1, hj⟩
  have hP : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U x ∩ S)) :=
    (A.chart j).isOpen_inter_preimage_symm ((Θ.isOpen_U x).inter hS)
  have hFs : ContDiffOn ℝ ∞ F ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U x ∩ S)) := by
    have h1 := (hΘ.1 x j).mono (fun z hz => ⟨hz.1, hz.2.1⟩ :
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U x ∩ S) ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x)
    have h2 := (hu j).mono (fun z hz => ⟨hz.1, hz.2.2⟩ :
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U x ∩ S) ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' S)
    exact (contDiffOn_const.mul h1).add h2
  have hτw : τ w₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Θ.U x ∩ S) := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j (Φ.symm w₀)) ∈ Θ.U x ∩ S
    rw [(A.chart j).left_inv hj]
    exact hw.2
  have hFa : ContDiffAt ℝ 2 F (τ w₀) :=
    (hFs.contDiffAt (hP.mem_nhds hτw)).of_le (WithTop.coe_le_coe.2 le_top)
  have hev : (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) =ᶠ[𝓝 w₀] F ∘ τ := by
    have h := (Φ.continuousAt_symm hw.1).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
    filter_upwards [h] with w hw'
    simp only [F, τ, Function.comp_apply, (A.chart j).left_inv hw']
  refine ⟨(hFa.comp w₀ hτa.restrictScalars.contDiffAt).congr_of_eventuallyEq hev, fun v => ?_⟩
  rw [levi_congr hev, levi_comp v hτa hFa]
  exact hN x j (τ w₀) hτw _

theorem isPsh_chart_sum : ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] (A : ReciprocityTheory.AnForm.M.FinHolAtlas D Y)
    (Θ : ReciprocityTheory.AnForm.M.LocPot Y) (u : Y → ℝ) (S : Set Y) (x : Y)
    (Φ : OpenPartialHomeomorph Y (Fin D → ℂ)), IsOpen S → ReciprocityTheory.AnForm.M.IsPotential A Θ →
    A.SmoothOn S u → GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.SumNonnegOn A Θ u S → ReciprocityTheory.AnForm.M.IsCompatChart A Φ →
    IsOpen (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) ∧
    ContinuousOn (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) ∧
    ReciprocityTheory.AnForm.A.IsPsh (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) ∧
    ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S))
      (fun w => max (2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) (-κ)) := by
  intro D Y _ A Θ u S x Φ hS hΘ hu hN hΦ
  have hT : IsOpen (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) :=
    Φ.isOpen_inter_preimage_symm ((Θ.isOpen_U x).inter hS)
  have hL := fun w (hw : w ∈ Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) =>
    local_form A Θ u S x Φ hS hΘ hu hN hΦ hw
  have hC : ContDiffOn ℝ 2 (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w))
      (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) := fun w hw => (hL w hw).1.contDiffWithinAt
  have hG : ReciprocityTheory.AnForm.A.IsPsh (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S))
      (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) :=
    (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ hT hC).2 ⟨hC, fun w hw v => (hL w hw).2 v⟩
  refine ⟨hT, hC.continuousOn, hG, fun κ => ?_⟩
  have hc : ReciprocityTheory.AnForm.A.IsPsh (Φ.target ∩ Φ.symm ⁻¹' (Θ.U x ∩ S)) fun _ => -κ :=
    ⟨upperSemicontinuousOn_const, fun z w _ =>
      ⟨circleIntegrable_const _ _ _, by rw [Real.circleAverage_const]⟩⟩
  have h := ReciprocityTheory.AnForm.A.isPsh_sup_thm D Bool _
    (fun b => if b then (fun w => 2 * Θ.φ x (Φ.symm w) + u (Φ.symm w)) else fun _ => -κ) hT
    (by rintro (_ | _) <;> simpa)
  convert h using 2 with w
  rw [← sup'_bool]
  congr 1
  funext b
  cases b <;> rfl

end GlobalTheory.ChartPsh
