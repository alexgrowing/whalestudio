import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∀ x : E, psi (inclE (F := F) (Ad F) x) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1) → ∀ (p : ℕ), p.Prime → SplitsIn E p → ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → ∀ e ∈ intV E v, e * e = e → e ≠ 0 → ∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((p : F)⁻¹) * (e * a))) ≠ 1 := by
  first | exact @GlobalTheory.St.G.psi_local_ne_one | exact GlobalTheory.St.G.psi_local_ne_one | (intros; apply GlobalTheory.St.G.psi_local_ne_one <;> assumption)
