import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccInvResidueCot
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot : ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im → Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  first | exact @GlobalTheory.tendsto_sum_Icc_inv_residue_cot | exact GlobalTheory.tendsto_sum_Icc_inv_residue_cot | (intros; apply GlobalTheory.tendsto_sum_Icc_inv_residue_cot <;> assumption)
