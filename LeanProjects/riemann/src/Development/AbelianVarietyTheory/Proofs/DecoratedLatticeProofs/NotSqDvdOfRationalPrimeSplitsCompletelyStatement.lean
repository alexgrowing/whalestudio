import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotSqDvdOfRationalPrimeSplitsCompletely
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_sq_dvd_of_rationalPrimeSplitsCompletely : ∀ (E : Type) [Field E] [NumberField E] (T : ℕ), T.Prime → GlobalTheory.St.G.SplitsIn E T → ∀ w : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ w.asIdeal → ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} := by
  first | exact @GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn | exact GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn | (intros; apply GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn <;> assumption)
