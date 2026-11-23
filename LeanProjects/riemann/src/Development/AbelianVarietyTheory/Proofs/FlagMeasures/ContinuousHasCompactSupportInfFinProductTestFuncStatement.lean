import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousHasCompactSupportInfFinProductTestFunc
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_hasCompactSupport_infFin_product_testFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n : ℕ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ), Continuous Φi → HasCompactSupport Φi → Continuous Φf → HasCompactSupport Φf → IsProdInfFin Φ Φi Φf → Continuous Φ ∧ HasCompactSupport Φ := by
  first | exact @GlobalTheory.prod_continuous_hasCompactSupport | exact GlobalTheory.prod_continuous_hasCompactSupport | (intros; apply GlobalTheory.prod_continuous_hasCompactSupport <;> assumption)
