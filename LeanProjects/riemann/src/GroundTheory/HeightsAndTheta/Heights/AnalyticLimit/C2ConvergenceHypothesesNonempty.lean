import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax Mollifier molli)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errE errorWithLinear ell)

noncomputable section

def ChartsCompareAt {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) (ρ : Mollifier D) (C t : ℝ) : Prop :=
  ∀ j k (x : X), x ∈ R.V' j → x ∈ R.V' k →
    |R.phChart R.φ ρ t j x - R.phChart R.φ ρ t k x| ≤ errorWithLinear C t

def GluedLocal.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (Cη : ℝ) (η : Fin R.n → X → ℝ),
    R.IsCutoffFamily Cη η → ∀ x₀ : X, ∃ (N : Set X) (J : Finset (Fin R.n)) (c : Fin R.n),
      IsOpen N ∧ x₀ ∈ N ∧ c ∈ J ∧ (∀ j ∈ J, N ⊆ R.V' j) ∧ N ⊆ R.V'' c ∧
      ∀ C t : ℝ, 0 < errorWithLinear C t → ChartsCompareAt R ρ C t → ∀ x ∈ N,
        R.glued R.φ ρ η C t x =
          @regMax (Fin R.n) _ ⟨c⟩ (errorWithLinear C t) (fun j => if j ∈ J then R.regArg R.φ ρ η C t j x
            else R.regArg R.φ ρ η C t c x - errorWithLinear C t) + errorWithLinear C t / 2

def ArgumentConvergenceC2.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (Cη : ℝ) (η : Fin R.n → X → ℝ),
    R.IsCutoffFamily Cη η → ∀ C : ℝ, 0 < C → ∀ (j : Fin R.n) (k : Fin A.n) (L : Set (Fin D → ℂ)),
      IsCompact L → L ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.Yo ∩ R.V' j) →
      ∃ U : Set (Fin D → ℂ), IsOpen U ∧ L ⊆ U ∧
        ContDiffOn ℝ 2 (fun y => R.φ ((A.chart k).symm y)) U ∧
        (∀ᶠ t in 𝓝[>] 0, ContDiffOn ℝ 2 (fun y => R.regArg R.φ ρ η C t j ((A.chart k).symm y)) U) ∧
        TendstoC2On (fun t y => R.regArg R.φ ρ η C t j ((A.chart k).symm y))
          (fun y => R.φ ((A.chart k).symm y)) L ∧
        ∃ M : ℝ, ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ L,
          ‖fderiv ℝ (fun y' => R.regArg R.φ ρ η C t j ((A.chart k).symm y')) y -
              fderiv ℝ (fun y' => R.φ ((A.chart k).symm y')) y‖ ≤ M * (t + errorWithLinear C t)

def PropertyF.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (Cη : ℝ) (η : Fin R.n → X → ℝ),
    R.IsCutoffFamily Cη η → ∀ C : ℝ, 0 < C →
    (∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ → ChartsCompareAt R ρ C t) →
    ∀ (k : Fin A.n) (K : Set (Fin D → ℂ)), IsCompact K →
      K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' R.Yo →
      TendstoC2On (fun t y => R.glued R.φ ρ η C t ((A.chart k).symm y))
        (fun y => R.φ ((A.chart k).symm y)) K

section Inhabitant

open ReciprocityTheory.AnForm.M (p1 projectiveLineChartAtZero projLineChart0_target projLineAtlas_chart0)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData projLineCutoff projLine_cutoffFamily mollifier_bounded_inhabited)

def p1j0 : Fin projLineChartData.n := ⟨0, by show 0 < 2; norm_num⟩

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
