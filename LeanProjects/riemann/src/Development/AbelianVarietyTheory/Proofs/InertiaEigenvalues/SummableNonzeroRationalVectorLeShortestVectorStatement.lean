import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ), Module.finrank ℝ (Fin a → Cinf E) ≤ N → ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A → (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J → c ξ = 0) → (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 → (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J → ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤ A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) → Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧ ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  first | exact @GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | exact GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | (intros; apply GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest <;> assumption)
