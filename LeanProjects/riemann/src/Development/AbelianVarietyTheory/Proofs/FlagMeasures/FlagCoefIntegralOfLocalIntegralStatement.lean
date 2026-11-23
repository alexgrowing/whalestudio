import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegral
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_coef_integral_of_local_integral : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T), IsFixedConv Λ g F → ∀ (j : ℕ) (x : S.V), x ∈ Xflag F j → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧ ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * w c = o := by
  first | exact @GlobalTheory.FlagCoef.coef_integral_of_flag | exact GlobalTheory.FlagCoef.coef_integral_of_flag | (intros; apply GlobalTheory.FlagCoef.coef_integral_of_flag <;> assumption)
