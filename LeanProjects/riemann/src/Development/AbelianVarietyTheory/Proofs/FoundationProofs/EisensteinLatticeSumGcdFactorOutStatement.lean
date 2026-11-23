import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOut
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out : ∀ (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) = LSeries (fun n => φ n) (j + 2 * s) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  first | exact @GlobalTheory.EisM.lattice_sum_gcd_out | exact GlobalTheory.EisM.lattice_sum_gcd_out | (intros; apply GlobalTheory.EisM.lattice_sum_gcd_out <;> assumption)
