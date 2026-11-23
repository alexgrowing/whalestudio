import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def IsInvForm {k r : ℕ} (R R' : Rep k r) (Bf : R.H → R'.H → ℂ) : Prop :=
  (∀ x ∈ R.sm, ∀ x' ∈ R.sm, ∀ y ∈ R'.sm, Bf (x + x') y = Bf x y + Bf x' y) ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (a • x) y = a * Bf x y) ∧
  (∀ x ∈ R.sm, ∀ y ∈ R'.sm, ∀ y' ∈ R'.sm, Bf x (y + y') = Bf x y + Bf x y') ∧
  (∀ (a : ℂ), ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x (a • y) = star a * Bf x y) ∧
  (∀ g ∈ GG k r, ∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf (R.σ g x) (R'.σ g y) = Bf x y) ∧
  ∃ (C : ℝ) (Ws Ws' : List (List (Mx k r))), (∀ W ∈ Ws ++ Ws', ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
    ∀ x ∈ R.sm, ∀ y ∈ R'.sm, ‖Bf x y‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W x‖).sum *
      (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W y‖).sum

def Poulsen : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r),
    R.IsDS ε mu → R'.IsDS ε mu' →
    (∀ Bf : R.H → R.H → ℂ, IsInvForm R R Bf → ∃ c : ℂ, ∀ x ∈ R.sm, ∀ y ∈ R.sm, Bf x y = c * ⟪y, x⟫_ℂ) ∧
    ∀ Bf : R.H → R'.H → ℂ, IsInvForm R R' Bf → (∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)

end BranchingSupport
