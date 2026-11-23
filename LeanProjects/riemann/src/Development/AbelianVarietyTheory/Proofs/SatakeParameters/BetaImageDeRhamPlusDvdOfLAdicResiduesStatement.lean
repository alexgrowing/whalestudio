import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaImageDeRhamPlusDvdOfLAdicResidues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.betaImageDeRhamPlus_dvd_of_lAdic_residues : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ y : Per.BdRp l, (∀ k : ℕ, ∃ s ∈ Sg ϖ, betaD ϖ ∣ y - ((l : ℕ) : Per.BdRp l) ^ k * s) → betaD ϖ ∣ y := by
  first | exact @GlobalTheory.Pst.StLat.betaD_dvd_of_res | exact GlobalTheory.Pst.StLat.betaD_dvd_of_res | (intros; apply GlobalTheory.Pst.StLat.betaD_dvd_of_res <;> assumption)
