import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, 0 ≤ c i) → ∑ i, c i • toReal (γ i) ∈ psdCone bar X := by
  first | exact @GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | exact GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | (intros; apply GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone <;> assumption)
