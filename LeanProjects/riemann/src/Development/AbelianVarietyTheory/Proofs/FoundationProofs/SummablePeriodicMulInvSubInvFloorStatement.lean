import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummablePeriodicMulInvSubInvFloor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_periodic_mul_inv_sub_inv_floor' : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → Summable (fun d : ℤ => φ d * ((z + d)⁻¹ - (z + (L * (d / L) : ℤ))⁻¹)) := by
  first | exact @GlobalTheory.summable_periodic_mul_inv_sub_inv_floor | exact GlobalTheory.summable_periodic_mul_inv_sub_inv_floor | (intros; apply GlobalTheory.summable_periodic_mul_inv_sub_inv_floor <;> assumption)
