import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart levi_base_indep)

noncomputable section

structure IsPullbackData {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    {B : FinHolAtlas D Y} {A : FinHolAtlas E Z} (R' : RegChartData B) (R : RegChartData A)
    (f : Y → Z) : Prop where
  holo : HoloMap B A f
  Yo_eq : R'.Yo = f ⁻¹' R.Yo
  r_eq : ∀ y ∈ R'.Yo, R'.r y = R.r (f y)
  φ_eq : ∀ y ∈ R'.Yo, R'.φ y = R.φ (f y)
  θ_eq : ∀ (x x' : Y) (k : Fin B.n),
    ∀ y ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (R'.θ.U x ∩ f ⁻¹' R.θ.U (f x')),
    ∀ w : Fin D → ℂ, levi (R'.θ.φ x ∘ (B.chart k).symm) y w =
      levi ((fun z => R.θ.φ (f x') (f z)) ∘ (B.chart k).symm) y w
  om_le : ∃ K : ℝ, ∀ (x x' : Y) (k : Fin B.n),
    ∀ y ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (R'.om.U x ∩ f ⁻¹' R.om.U (f x')),
    ∀ w : Fin D → ℂ, levi ((fun z => R.om.φ (f x') (f z)) ∘ (B.chart k).symm) y w ≤
      K * levi (R'.om.φ x ∘ (B.chart k).symm) y w

def C2ConvOn {E : ℕ} {Z : Type} [TopologicalSpace Z] (A : FinHolAtlas E Z) (V : Set Z)
    (g : ℝ → Z → ℝ) (φ : Z → ℝ) : Prop :=
  ∀ (k : Fin A.n) (K : Set (Fin E → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V →
    TendstoUniformlyOn (fun t y => g t ((A.chart k).symm y)) (fun y => φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K

def C2ConvergencePullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (B : FinHolAtlas D Y)
    (A : FinHolAtlas E Z) (f : Y → Z), HoloMap B A f →
    ∀ (V : Set Z), IsOpen V → ∀ (g : ℝ → Z → ℝ) (φ : Z → ℝ) (φ' : Y → ℝ),
      A.SmoothOn V φ → (∀ y ∈ f ⁻¹' V, φ' y = φ (f y)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (g t)) →
      C2ConvOn A V g φ → C2ConvOn B (f ⁻¹' V) (fun t => g t ∘ f) φ'

def SystemPullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {B : FinHolAtlas D Y}
    {A : FinHolAtlas E Z} (R' : RegChartData B) (R : RegChartData A) (f : Y → Z),
    IsPullbackData R' R f → ∀ S : System R, ∃ S' : System R', ∀ t y, S'.ph t y = S.ph t (f y)

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
