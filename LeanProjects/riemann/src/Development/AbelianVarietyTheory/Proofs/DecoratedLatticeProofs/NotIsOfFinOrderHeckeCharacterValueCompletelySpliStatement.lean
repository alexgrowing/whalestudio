import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
open NumberField IsDedekindDomain Formalism.BasicNotions

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  first | exact @GlobalTheory.SplitValuePow.not_isOfFinOrder_val | exact GlobalTheory.SplitValuePow.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValuePow.not_isOfFinOrder_val <;> assumption)
