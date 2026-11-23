import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

theorem maDens_congr_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) y = fderiv ℝ (fderiv ℝ (ψ i)) y := (h i).fderiv.fderiv_eq
    unfold hessC
    simp only [h2]
    rfl
  simp only [maDens, hH]

theorem holoMap_preimage_mem_nhds {e e' : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) ∈ 𝓝 y := by
  have hs : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  exact ((B.chart j).isOpen_inter_preimage_symm hs).mem_nhds ⟨hy, hk⟩

theorem potential_contDiffAt_chart {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hS : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) :=
    (A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)
  refine ((hP.1 x k).contDiffAt (hS.mem_nhds ⟨hz, hzU⟩)).of_le ?_
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

theorem pullback_local_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h)
    (P : LocPot X) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (fun y' => P.φ (h ((B.chart j).symm y)) (h ((B.chart j).symm y'))) =ᶠ[𝓝 y]
      (P.φ (h ((B.chart j).symm y)) ∘ (A.chart k).symm) ∘
        (A.chart k ∘ h ∘ (B.chart j).symm) := by
  filter_upwards [holoMap_preimage_mem_nhds hh j k hy hk] with y' hy'
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv hy'.2]

theorem locDensPullback : LocDensPullbackStatement := by
  intro e X Y _ _ A B h hh Φ hΦ j k y hy hk
  set x0 := h ((B.chart j).symm y) with hx0
  set τ := A.chart k ∘ h ∘ (B.chart j).symm with hτ
  have hτa : AnalyticAt ℂ τ y := hh.2 j k y ⟨hy, hk⟩
  have hτy : τ y = A.chart k x0 := rfl
  have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
  have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm) (τ y) := by
    intro i
    rw [hτy]
    exact potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
      (by rw [hsymm]; exact (Φ i).mem_U x0)
  unfold locDens
  refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
  rw [hsymm]
  refine (ReciprocityTheory.AnForm.A.maDens_comp (fun i => (Φ i).φ x0 ∘ (A.chart k).symm) τ y hτa hφ).trans ?_
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hτy]
  rfl

theorem rankDrop : RankDropStatement := by
  intro e e' X Y _ _ A B h hh hrk Φ hΦ g
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_eq_zero fun j _ => ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
    set x0 := h ((B.chart j).symm y) with hx0
    have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
    have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm)
        ((A.chart k ∘ h ∘ (B.chart j).symm) y) := fun i =>
      potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
        (by simp only [Function.comp_apply]; rw [hsymm]; exact (Φ i).mem_U x0)
    have h0 : locDens B (fun i => (Φ i).pullback h hh.1) j y = 0 := by
      unfold locDens
      refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
      exact maDens_comp_eq_zero_of_rank_lt _ _ y (hh.2 j k y ⟨hy, hk⟩) hφ (hrk j k y hy hk)
    rw [h0, mul_zero]
  · rfl

end

end ReciprocityTheory.AnForm.M
