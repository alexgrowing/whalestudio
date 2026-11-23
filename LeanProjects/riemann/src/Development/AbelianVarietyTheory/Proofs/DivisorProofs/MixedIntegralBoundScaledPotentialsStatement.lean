import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralBoundScaledPotentials
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_bound_scaled_potentials : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Om : LocPot X) (w : X → ℝ) (u : Fin e → X → ℝ) (M : ℝ), 1 ≤ M → IsPotential A Om → IsPsh A Om → A.Smooth w → (∀ x, w x ≤ 0) → IsPsh A (Om + LocPot.ofFun w) → (∀ i, A.Smooth (u i) ∧ (∀ x, -M ≤ u i x ∧ u i x ≤ 0) ∧ IsPsh A (Om + LocPot.ofFun (u i))) → mInt A (fun i => Om + LocPot.ofFun (u i)) (fun x => -w x) ≤ M ^ e * (mInt A (fun _ => Om) (fun x => -w x) + e * mInt A (fun _ => Om) (fun _ => 1)) := by
  first | exact @GlobalTheory.PotOsc.mInt_le_pow_mul | exact GlobalTheory.PotOsc.mInt_le_pow_mul | (intros; apply GlobalTheory.PotOsc.mInt_le_pow_mul <;> assumption)
