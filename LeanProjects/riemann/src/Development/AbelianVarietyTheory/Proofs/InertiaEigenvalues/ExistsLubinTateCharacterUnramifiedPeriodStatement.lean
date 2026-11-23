import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lubinTate_character_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  first | exact @GlobalTheory.LTChar.main | exact GlobalTheory.LTChar.main | (intros; apply GlobalTheory.LTChar.main <;> assumption)
