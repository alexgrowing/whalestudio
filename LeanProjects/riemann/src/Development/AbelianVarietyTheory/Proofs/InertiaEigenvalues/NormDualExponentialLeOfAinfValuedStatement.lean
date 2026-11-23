import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDualExponentialLeOfAinfValued
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_dualExponential_le_of_ainf_valued : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ (z : GQ l → ℚ_[l]) (α : Om l), α ∈ Ks K s → ExpStar D.loc (Gj K s) e z α → (∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR (z σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1)) → ‖α‖ ≤ (l : ℝ) ^ (((e * (s + 1) + padicValNat l e.factorial + 1 + s : ℕ) : ℝ) + (e : ℝ) / ((l : ℝ) - 1)) := by
  first | exact @GlobalTheory.Cyc.ExpBound.norm_expStar_le | exact GlobalTheory.Cyc.ExpBound.norm_expStar_le | (intros; apply GlobalTheory.Cyc.ExpBound.norm_expStar_le <;> assumption)
