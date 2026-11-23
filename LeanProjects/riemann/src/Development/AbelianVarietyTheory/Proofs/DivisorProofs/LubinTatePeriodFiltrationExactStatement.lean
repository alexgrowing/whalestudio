import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTatePeriodFiltrationExact
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_period_filtration_exact : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (Y : P.R.BdR),
    (∀ g : ↥(GK K), (P.PD K).actdR g Y = algebraMap ↥K.1 P.R.BdR (χ g : ↥K.1) * Y) →
    Y ∈ (P.PD K).Fil 1 → Y ∉ (P.PD K).Fil 2 →
    ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ⁻¹)) τ₀,
      x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 ∧
      x ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 2 := by
  first | exact @GlobalTheory.PMC.PeriodVector.exists_degree_one | exact GlobalTheory.PMC.PeriodVector.exists_degree_one | (intros; apply GlobalTheory.PMC.PeriodVector.exists_degree_one <;> assumption)
