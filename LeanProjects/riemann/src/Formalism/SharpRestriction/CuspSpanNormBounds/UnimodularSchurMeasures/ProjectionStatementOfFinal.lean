import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuCountOfPack

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cu.LocGrowth (X : CData) : Prop :=
  ∀ (v : InfinitePlace X.I.F) (s : ℝ), 0 ≤ s →
    (1 ≤ q0At X.I v →
      2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + s < X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ))) →
    Integrable (fun g : Formalism.REAL.UJ (X.I.ε v) =>
      ‖coefOn (X.σ v) (X.w v) (X.w v) g‖ * Real.exp (s * cartanDistance (X.I.ε v) g)) (Formalism.REAL.muG (X.I.ε v))

theorem cu_haarGrowth_of (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (hL : cu.LocGrowth X) : cu.HaarGrowth X := by
  intro s hs hrate
  have he : Integrable X.e X.μf := hX.2.1.2.2.2.2.2.2.1
  have h1 : Integrable (fun g : X.I.Ginf => ∏ v, (‖coefOn (X.σ v) (X.w v) (X.w v) (g v)‖ *
      Real.exp (s * cartanDistance (X.I.ε v) (g v)))) (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) :=
    Integrable.fintype_prod_dep (μ := fun v => Formalism.REAL.muG (X.I.ε v))
      (f := fun v g => ‖coefOn (X.σ v) (X.w v) (X.w v) g‖ * Real.exp (s * cartanDistance (X.I.ε v) g))
      (fun v => hL v s hs (hrate v))
  have h2 := (h1.const_mul (fdegAll X.I X.σ X.w)).mul_prod he.norm
  refine h2.congr (Filter.Eventually.of_forall fun g => ?_)
  show fdegAll X.I X.σ X.w * (∏ v, (‖coefOn (X.σ v) (X.w v) (X.w v) (g.1 v)‖ *
      Real.exp (s * cartanDistance (X.I.ε v) (g.1 v)))) * ‖X.e g.2‖ = ‖X.φ g‖ * cu_wt X s g
  unfold CData.φ phe phOf cu_wt
  rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.fdegAll_nonneg,
    Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
  ring

def cu.Last (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.LocGrowth X ∧ (∃ S : CSize X, S.Strata ∧ S.PackCount ∧ S.Inv ∧ S.Lip ∧ S.LowN) ∧ X.KernelDiag ∧
    UnimodA X

theorem cu_core_of_last (X : CData) {n₀ : ℕ} {A : ℝ} (hn₀ : 1 ≤ n₀) (hX : X.HypB n₀ A) (h : cu.Last X) : cu.Core X := by
  obtain ⟨sU, sL, ⟨S, a1, a2, a3, a4, a5⟩, sK, sA⟩ := h
  exact ⟨sU, cu_haarGrowth_of X hX sL, cu_sizeStep_of X (le_trans hn₀ hX.1.1) S a1 a2 a3 a4 a5, sK, sA⟩

def cu_StepsLast (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.Last X

theorem cuspidal_range_of_final_facts (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A C : ℝ} (hn₀ : 1 ≤ n₀)
    (hC : 46 ≤ C) (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) (h2 : X.GapAboveSquareRootThreshold C) (hE : X.LowProj) (hF : cu.FinStep X)
    (hS : cu.Last X) : X.CuspStep :=
  cuspidal_range_of_reduced_facts X D hdec hn₀ hC hX h1 h2 hE hF (cu_core_of_last X hn₀ hX hS)

end Formalism.MainNotions.LeviCoordinates
