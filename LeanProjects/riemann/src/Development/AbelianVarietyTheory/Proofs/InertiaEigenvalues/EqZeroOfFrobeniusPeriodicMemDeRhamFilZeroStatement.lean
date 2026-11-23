import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfFrobeniusPeriodicMemDeRhamFilZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_frobenius_periodic_mem_deRhamFil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h d : ℕ), 0 < h → 0 < d → ∀ c : P.R.B, (l : P.R.B) ^ d * P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) → c = 0 := by
  first | exact @GlobalTheory.PMon.no_fil_zero_neg_slope | exact GlobalTheory.PMon.no_fil_zero_neg_slope | (intros; apply GlobalTheory.PMon.no_fil_zero_neg_slope <;> assumption)
