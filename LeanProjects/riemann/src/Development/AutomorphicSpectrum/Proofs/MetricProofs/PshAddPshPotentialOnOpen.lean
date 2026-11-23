import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSetStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PshAdd

open ReciprocityTheory.AnForm.M.LocPot

theorem isPshOn_add_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X)
    (P : LocPot X) (f : X → ℝ) (Θ : LocPot X) (hU : IsOpen U) (hP : IsPotential A P)
    (hΘ : IsPotential A Θ) (hf : A.SmoothOn U f) (hPf : IsPshOn A U (P + LocPot.ofFun f))
    (hΘp : IsPsh A Θ) : IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  intro x j y hy w
  obtain ⟨hyt, ⟨⟨hyP, -⟩, hyΘ⟩, hyU⟩ := hy
  have hP2 : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hyt, hyP⟩
    exact ((hP.1 x j).contDiffAt hmem).of_le (by norm_cast)
  have hf2 : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' U ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hyt, hyU⟩
    exact ((hf j).contDiffAt hmem).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U x)).mem_nhds ⟨hyt, hyΘ⟩
    exact ((hΘ.1 x j).contDiffAt hmem).of_le (by norm_cast)
  have hPf2 : ContDiffAt ℝ 2 (fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) y :=
    hP2.add hf2
  have h1 := hPf x j y ⟨hyt, ⟨hyP, Set.mem_univ _⟩, hyU⟩ w
  have h2 := hΘp x j y ⟨hyt, hyΘ⟩ w
  have hsum := ReciprocityTheory.AnForm.levi_add_smul (f := fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z))
    (g := Θ.φ x ∘ (A.chart j).symm) 1 hPf2 hΘ2 w
  have heq : ((P + LocPot.ofFun f + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) +
        1 * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z; simp [Function.comp, HAdd.hAdd, Add.add, LocPot.ofFun]
  rw [heq, hsum, one_mul]
  exact add_nonneg h1 h2

end GlobalTheory.CompanionTheory.Ar.PshAdd
