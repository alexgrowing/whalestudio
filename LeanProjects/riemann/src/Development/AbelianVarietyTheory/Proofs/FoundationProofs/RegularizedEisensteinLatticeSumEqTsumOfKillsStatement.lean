import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumEqTsumOfKills
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills : ∀ (j L : ℕ) (s : ℝ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖) ∧ lat j s L v Φ τ = ∑' x : ℤ × ℤ, Φ x * trm j s ((x.1 : ℂ) * τ + x.2) := by
  first | exact @GlobalTheory.EisM.lat_eq_tsum_of_kills | exact GlobalTheory.EisM.lat_eq_tsum_of_kills | (intros; apply GlobalTheory.EisM.lat_eq_tsum_of_kills <;> assumption)
