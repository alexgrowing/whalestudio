import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlocksTwistedConjBlockUpperTriangular
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  first | (exact @GlobalTheory.Shin.BlocksTwist.blocks_twist) | (exact GlobalTheory.Shin.BlocksTwist.blocks_twist) | (intros; apply GlobalTheory.Shin.BlocksTwist.blocks_twist <;> assumption)
