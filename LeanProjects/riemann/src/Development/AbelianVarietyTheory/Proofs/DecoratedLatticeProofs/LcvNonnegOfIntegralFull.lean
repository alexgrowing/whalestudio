import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem lcv_nonneg_of_integral_full :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (j : ℕ) (Γ : Matrix (Fin j) (Fin j) K) (Y : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (L : Submodule (𝓞 K) (Fin j → K)), (∀ v, IsUnit (Y v).det) → Submodule.IsLattice K L → Γ.det ≠ 0 → Formalism.HermitianLatticesTheory.IsIntegralLat (R := 𝓞 K) (hform Γ) L → (∏ v : InfinitePlace K, ‖v.embedding Γ.det‖ ≤ ∏ v : InfinitePlace K, (gram Y v (fun i => (Pi.single i 1 : Fin j → K))).det.re) → 0 ≤ lcv Y L := by
  intro K _ _ _ _ j Γ Y L hY hL hΓ hint hle
  have h := GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j Y hY Γ 1 one_pos hΓ hle L hL (by
    intro x hx y hy
    have h1 := hint x hx y hy
    rw [RationalHermitianForm.hform_eq_dot] at h1
    simpa using h1)
  simpa using h

end GlobalTheory
