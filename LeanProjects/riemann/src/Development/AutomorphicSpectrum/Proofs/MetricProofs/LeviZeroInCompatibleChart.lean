import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_eq_zero_of_compatChart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ →
    IsOpen U → A.SmoothOn U g →
    (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w,
      levi (g ∘ (A.chart j).symm) y w = 0) →
    ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  intro e X _ A ψ U g hψ hU hg hA z hz hzU w
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hzs : z ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source := ⟨hz, hj⟩
  have hopen : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart j).open_source
  have hτ : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) z := (hψ j).2 z hzs
  have hEq : g ∘ ⇑ψ.symm =ᶠ[𝓝 z] (g ∘ ⇑(A.chart j).symm) ∘ (⇑(A.chart j) ∘ ⇑ψ.symm) := by
    filter_upwards [hopen.mem_nhds hzs] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy.2]
  have hcz : (⇑(A.chart j) ∘ ⇑ψ.symm) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, Function.comp_apply, (A.chart j).left_inv hj]
    exact hzU
  have hopen2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  have hsm : ContDiffAt ℝ 2 (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) z) :=
    ((hg j).contDiffAt (hopen2.mem_nhds hcz)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | norm_num | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  rw [levi_congr hEq w, levi_comp w hτ hsm]
  exact hA j _ hcz _

end GlobalTheory.CompanionTheory.LeviChart
