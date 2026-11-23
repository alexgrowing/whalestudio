import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRapidDecayOneSimpleRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a → (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) → ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ Ω : Set (GA E a), IsCompact Ω → Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) → ∀ (t C₀ : ℝ) (N₀ : ℕ), 0 < t → (∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C₀ * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀) → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ i j : Fin a, (j : ℕ) = i + 1 → ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤ C * (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := by
  first | exact @GlobalTheory.HCF.Decay.decay | exact GlobalTheory.HCF.Decay.decay | (intros; apply GlobalTheory.HCF.Decay.decay <;> assumption)
