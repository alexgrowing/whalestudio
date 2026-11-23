import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyMaximalCompactCasimirKillsKType
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_maximalCompactCasimir_kills_KType : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (W : Submodule ℂ (Kinf E a → ℂ)),
    FiniteDimensional ℂ W → ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∀ φ : Sm E a,
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) → Polynomial.aeval (casKOp E a) q φ = 0 := by
  first | exact @GlobalTheory.HCKTypes.exists_casK_poly | exact GlobalTheory.HCKTypes.exists_casK_poly | (intros; apply GlobalTheory.HCKTypes.exists_casK_poly <;> assumption)
