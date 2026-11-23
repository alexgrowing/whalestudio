import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
import Mathlib
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨ (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by
  first | exact @GlobalTheory.quadratic_unramified_iff_inert_or_split | exact GlobalTheory.quadratic_unramified_iff_inert_or_split | (intros; apply GlobalTheory.quadratic_unramified_iff_inert_or_split <;> assumption)
