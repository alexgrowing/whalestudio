import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

def IsShiftSys {K : Type} [NormedField K] [DecidableEq K] (W : WeierstrassCurve K)
    (A : AddSubgroup W.toAffine.Point) (S : W.toAffine.Point) (H : W.toAffine.Point → K⟦X⟧)
    (c : W.toAffine.Point → K) : Prop :=
  OneUnit (H 0) ∧ (∀ Q ∈ A, Q ≠ 0 → c Q ≠ 0) ∧
  ∀ P ∈ A, ∀ Q ∈ A, Q ≠ 0 → ∃ ρ : K, ‖ρ‖ = 1 ∧
    H (P + Q) * H (P - Q) = C (ρ * c Q ^ 2) * (C (px W Q) - xT W (P + S)) * H P ^ 2

def ShiftUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A →
    (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) →
    (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1) →
    ∀ (H : W.toAffine.Point → K⟦X⟧) (c : W.toAffine.Point → K), IsShiftSys W A S H c →
      (∀ Q ∈ A, Q ≠ 0 → ‖c Q‖ = 1) ∧
      ∀ P ∈ A, ‖constantCoeff (H P)‖ = 1 ∧ OneUnit (C (constantCoeff (H P))⁻¹ * H P)

def ShiftPtsInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ (A : AddSubgroup W.toAffine.Point) [Finite A], ‖(Nat.card A : K)‖ = 1 →
    ∀ (S : W.toAffine.Point), S ∉ A → S + S = 0 → ‖px W S‖ ≤ 1 → ‖py W S‖ ≤ 1 →
      (∀ Q ∈ A, Q ≠ 0 → ‖px W Q‖ ≤ 1 ∧ ‖py W Q‖ ≤ 1) ∧
      (∀ P ∈ A, ‖px W (P + S)‖ ≤ 1 ∧ ‖py W (P + S)‖ ≤ 1)

end Formalism.L2.Th1.E
