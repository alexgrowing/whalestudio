import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeNilRadicalInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_nil_radical_invariant : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (x : Fin n → ℂ) (N : Subgroup G), (∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N) → ∀ f : smLoc J s, (∀ ν ∈ N, ∀ g, f.1 (ν * g) = f.1 g) → ∀ T ∈ leftIdl ρ (nilRad J x : Set (Matrix (Fin n) (Fin n) ℂ)), (T f).1 1 = 0 := by
  first | exact @GlobalTheory.TorFin.leftIdl_apply_one_eq_zero | exact GlobalTheory.TorFin.leftIdl_apply_one_eq_zero | (intros; apply GlobalTheory.TorFin.leftIdl_apply_one_eq_zero <;> assumption)
