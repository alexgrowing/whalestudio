import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNeg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingSign_alternate_of_sign_neg : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 → Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧ Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  first | exact @GlobalTheory.signs_alternate_inert | exact GlobalTheory.signs_alternate_inert | (intros; apply GlobalTheory.signs_alternate_inert <;> assumption)
