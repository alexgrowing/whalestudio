import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilate
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  first | exact @GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | exact GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | (intros; apply GlobalTheory.AdelicCharDilate.exists_eq_std_dilate <;> assumption)
