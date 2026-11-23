import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusion
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ), LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  first | exact @GlobalTheory.ExpTie.jexpU_le_of_lIncl | exact GlobalTheory.ExpTie.jexpU_le_of_lIncl | (intros; apply GlobalTheory.ExpTie.jexpU_le_of_lIncl <;> assumption)
