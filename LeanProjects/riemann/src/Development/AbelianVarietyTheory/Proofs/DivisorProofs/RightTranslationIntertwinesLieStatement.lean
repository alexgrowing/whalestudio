import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationIntertwinesLie
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translation_intertwines_lie : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (u : Matrix (Fin n) (Fin n) ℂ) (b : G), IsUni J u → (∀ v, IsUni J v → b * s v = s v * b) → ∃ r : Module.End ℂ (smLoc J s), (∀ (f : smLoc J s) (g : G), (r f).1 g = f.1 (g * (s u * b))) ∧ ∀ Y, r * ρ Y = ρ (u * Y * u⁻¹) * r := by
  first | exact @GlobalTheory.TorFin.RightTr.exists_rightTranslation | exact GlobalTheory.TorFin.RightTr.exists_rightTranslation | (intros; apply GlobalTheory.TorFin.RightTr.exists_rightTranslation <;> assumption)
