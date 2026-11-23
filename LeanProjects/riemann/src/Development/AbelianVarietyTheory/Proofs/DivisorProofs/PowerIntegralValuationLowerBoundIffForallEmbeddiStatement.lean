import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddi
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  first | exact @GlobalTheory.LadicDenom.valGe_iff_forall_sz | exact GlobalTheory.LadicDenom.valGe_iff_forall_sz | (intros; apply GlobalTheory.LadicDenom.valGe_iff_forall_sz <;> assumption)
