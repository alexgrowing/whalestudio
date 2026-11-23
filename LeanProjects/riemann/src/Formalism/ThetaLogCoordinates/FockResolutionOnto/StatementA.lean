import Formalism.ThetaLogCoordinates.FockResolutionOnto.ShiftLastLetterThresholds

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def PartnerDet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (k : ℕ) (g : Fin k → Vs) (D : ℝ),
    LinearIndependent ℤ_[p] g →
    (∀ u ∈ Submodule.span ℤ_[p] (Set.range g),
      (∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a) →
      ∃ u' ∈ Submodule.span ℤ_[p] (Set.range g), (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    (p : ℝ) ^ (-(D * k)) ≤ ‖(Matrix.of fun a b => be (g a) (g b)).det‖

def GradedPieceBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e D c : ℕ) (κ : ℝ),
    ProjAt p LLw J M ρ w e D → SatAt p LLw J M ρ w e c → ((D + 2 * c : ℕ) : ℝ) ≤ κ →
    ∀ (k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
      (p : ℝ) ^ (-(κ * k)) ≤
        ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖

end Formalism.InvariantFactorPaths.L4
