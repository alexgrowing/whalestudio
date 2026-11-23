import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
open scoped ENNReal

namespace GlobalTheory.PshPull

theorem isPsh_pullback : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (n : ℕ) (Y : Type)
    [TopologicalSpace Y] (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (P : LocPot X),
    IsPotential A P → IsPsh A P → IsPsh B (P.pullback μ hμ.1) := by
  intro d X _ A n Y _ B μ hμ P hP hp y j t ht w
  obtain ⟨k, hk⟩ := A.cover (μ ((B.chart j).symm t))
  have hO : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hμ.1)
  have htO : t ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (μ ⁻¹' (A.chart k).source) := ⟨ht.1, hk⟩
  have han := hμ.2 j k t htO
  have hin : (A.chart k ∘ μ ∘ (B.chart j).symm) t ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U (μ y) := by
    refine ⟨(A.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (A.chart k).left_inv hk]
    exact ht.2
  have h1 : ContDiffAt ℝ 2 (P.φ (μ y) ∘ (A.chart k).symm) ((A.chart k ∘ μ ∘ (B.chart j).symm) t) :=
    (contDiffAt_of_isPotential A P hP (μ y) k hin).of_le (by norm_cast)
  have heq : (P.pullback μ hμ.1).φ y ∘ (B.chart j).symm =ᶠ[𝓝 t]
      (P.φ (μ y) ∘ (A.chart k).symm) ∘ (A.chart k ∘ μ ∘ (B.chart j).symm) := by
    filter_upwards [hO.mem_nhds htO] with t' ht'
    show P.φ (μ y) (μ ((B.chart j).symm t')) =
      P.φ (μ y) ((A.chart k).symm ((A.chart k) (μ ((B.chart j).symm t'))))
    rw [(A.chart k).left_inv ht'.2]
  rw [levi_congr heq, levi_comp w han h1]
  exact hp _ k _ hin _

end GlobalTheory.PshPull
