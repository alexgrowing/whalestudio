import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLaRingOfIntegers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingFw
open NumberField GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_La_ringOfIntegers' : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p), letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O); Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  first | (exact @GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers) | (exact GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers) | (intros; apply GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers <;> assumption)
