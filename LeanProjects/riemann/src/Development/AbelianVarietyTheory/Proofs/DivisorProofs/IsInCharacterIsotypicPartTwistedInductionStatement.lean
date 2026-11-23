import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartTwistedInduction
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y → Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  first | (exact @GlobalTheory.Shin.IndIso.kills_ind) | (exact GlobalTheory.Shin.IndIso.kills_ind) | (intros; apply GlobalTheory.Shin.IndIso.kills_ind  <;> assumption)
