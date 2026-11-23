import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocalGeneratorAtBasePrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_localGenerator_at_basePrime : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 → ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ a : D.host.E, a ≠ 0 ∧ ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ ((c : D.host.F) : D.host.E) * a ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a * (o : D.host.E) := by
  first | exact @GlobalTheory.fracIdeal_locGen | exact GlobalTheory.fracIdeal_locGen | (intros; apply GlobalTheory.fracIdeal_locGen <;> assumption)
