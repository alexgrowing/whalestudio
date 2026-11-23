import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

namespace GlobalTheory.OTY.TwEst

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def wt (A : WeightedAtlas n Y ι La) (E : La) (β : ι → Y → ℂ) (z : Y → V n) (y : Y) : ℝ :=
  -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap (jdet A z) y)

def quot (A : WeightedAtlas n Y ι La) (h β : ι → Y → ℂ) (y : Y) : ℂ :=
  h (A.pick y) y / β (A.pick y) y

open scoped Classical in

def ext0 {Y : Type*} (U : Set Y) (f : U → ℂ) (y : Y) : ℂ :=
  if hy : y ∈ U then f ⟨y, hy⟩ else 0

theorem extendByZeroOnSubset_apply_coe {Y : Type*} (U : Set Y) (f : U → ℂ) (y : U) : ext0 U f y = f y := by
  simp [ext0, y.2]

end

end GlobalTheory.OTY.TwEst

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.nz_facts {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (L Λ : La) (s : Fin n → ι → Y → ℂ) (τ : ι → Y → ℂ) (C : ℝ) (hC0 : 0 < C)
    (hsq : ∀ y, A.sqn L s y ≤ 1) (hC : ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) (y : Y) (hy : y ∈ nz A τ) :
    y ∉ A.zeroSet s ∧ psi A L s y ≤ 0 ∧
      -psi A L s y ≤ (n : ℝ) * (-Real.log (A.nsq Λ τ y)) + (n : ℝ) * Real.log C := by
  have hτy : τ (A.pick y) y ≠ 0 := hy
  have hτ0 : 0 < A.nsq Λ τ y := by
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr hτy) 2) (Real.exp_pos _)
  have hs0 : 0 < A.sqn L s y := by
    by_contra hle
    push_neg at hle
    have := hC y
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hz' : ∀ k, s k (A.pick y) y = 0 := hz
    have : A.sqn L s y = 0 := by
      unfold WeightedAtlas.sqn WeightedAtlas.nsq
      simp [hz']
    linarith
  · unfold psi
    have := Real.log_nonpos hs0.le (hsq y)
    nlinarith
  · unfold psi
    have h1 : Real.log (A.nsq Λ τ y) ≤ Real.log C + Real.log (A.sqn L s y) := by
      rw [← Real.log_mul hC0.ne' hs0.ne']
      exact Real.log_le_log hτ0 (hC y)
    have := mul_le_mul_of_nonneg_left h1 hn
    nlinarith
