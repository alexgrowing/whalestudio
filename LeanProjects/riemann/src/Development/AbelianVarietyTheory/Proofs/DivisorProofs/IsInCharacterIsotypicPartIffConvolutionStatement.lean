import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartIffConvolution
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y → (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  first | (exact @GlobalTheory.Shin.kills_iff_conv) | (exact GlobalTheory.Shin.kills_iff_conv) | (intros; apply GlobalTheory.Shin.kills_iff_conv <;> assumption)
