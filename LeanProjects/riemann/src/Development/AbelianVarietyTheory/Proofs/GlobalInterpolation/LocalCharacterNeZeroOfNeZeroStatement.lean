import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharacterNeZeroOfNeZero
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCharacter_ne_zero_of_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 → LocE.locChar (qOf P) cq χ a ≠ 0 := by
  first | exact @GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero | exact GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero | (intros; apply GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero <;> assumption)
