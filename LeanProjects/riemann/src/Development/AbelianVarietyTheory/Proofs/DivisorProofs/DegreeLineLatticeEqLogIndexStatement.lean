import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLineLatticeEqLogIndex
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_line_lattice_eq_log_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) (a : K), L.FG → x ≠ 0 → a ≠ 0 → a • x ∈ L → (Module.finrank ℚ K : ℝ) * deg h (lineLat L x) + ∑ σ : K →+* ℂ, Real.log (h.nrm σ x) = Real.log ((Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex (L.comap ((LinearMap.toSpanSingleton K (Fin m → K) x).restrictScalars (𝓞 K))).toAddSubgroup : ℝ) - ∑ σ : K →+* ℂ, Real.log ‖σ a‖ := by
  first | exact @GlobalTheory.finrank_mul_deg_lineLat_add_sum_log_nrm | exact GlobalTheory.finrank_mul_deg_lineLat_add_sum_log_nrm | (intros; apply GlobalTheory.finrank_mul_deg_lineLat_add_sum_log_nrm <;> assumption)
