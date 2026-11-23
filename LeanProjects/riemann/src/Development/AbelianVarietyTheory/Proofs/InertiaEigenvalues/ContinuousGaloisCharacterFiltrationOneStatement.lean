import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterFiltrationOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitCont
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_galois_character_filtration_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  first | exact @GlobalTheory.LTChar.char_cont | exact GlobalTheory.LTChar.char_cont | (intros; apply GlobalTheory.LTChar.char_cont <;> assumption)
