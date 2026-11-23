import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLatticeQuotPrime
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lattice_quot_prime : ∀ (I : AutInst) (p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)), p.Prime → Ideal.absNorm w.asIdeal = p → Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf))) = p ^ I.n := by
  first | exact @GlobalTheory.AdelicLattice.card_quot_extId | exact GlobalTheory.AdelicLattice.card_quot_extId | (intros; apply GlobalTheory.AdelicLattice.card_quot_extId <;> assumption)
