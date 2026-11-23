import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.ThirdJetIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)

def CurveEndoUnitBall : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K], ‖(2 : K)‖ = 1 →
    ∀ (W : WeierstrassCurve K), Formalism.L2.Th1.A.IntModel W → ∀ s2 : K,
    ∀ (O : Type) [CommRing O] [StarRing O] [TopologicalSpace O] (τ : O →+* K),
    Continuous τ → Continuous (star : O → O) →
    (∀ z : O, star z = z → τ z ∈ closure (Set.range (fun n : ℤ => (n : K)))) →
    IsUnit (2 : O) → (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    ∀ Dn : Set O, (∀ α : Oˣ, (α : O) ∈ closure Dn) →
    (∀ α ∈ Dn, ∃ (ι : Type) (_ : Fintype ι) (neg : ι → ι) (xP yP : ι → K),
      IsEndoCurve W neg xP yP (τ α) ∧ (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      τ α * τ (star α) = (Fintype.card ι : K) + 1 ∧ ‖τ α‖ = 1 ∧
      ‖((τ α) ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 ∧
      τ α * (τ α - τ (star α)) * s2 = ∑ P, (xP P + W.b₂ / 12)) →
    (∀ α : O, EndInt (Formalism.G.unitBall K) (logSer W) (expSer W) (τ α) ∧
      PhNormAt (Formalism.G.unitBall K) (logSer W) (expSer W)
        (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (τ α) (τ (star α)) ∧
      AdjAt (Formalism.G.unitBall K) (logSer W) (expSer W)
        (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (τ α) (τ (star α)) ∧
      ‖(τ α - τ (star α)) * jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) 2‖ ≤ 1) ∧
    (∃ H : PowerSeries K, (∀ i : ℕ, ‖jet (logSer W) H i‖ ≤ 1) ∧
      (mvExp (-(Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W))) : PowerSeries K) =
        mvExp (-(PowerSeries.C (jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) 2 / 2)
          * (logSer W) ^ 2)) * H) ∧
    (∀ α : O, ‖τ α - τ (star α)‖ = 1 → ∀ i : ℕ,
      ‖jet (logSer W) (mvExp (-(Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W))) : PowerSeries K) i‖ ≤ 1)

def CurveJetsUnitBall : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K], ‖(2 : K)‖ = 1 →
    ∀ (W : WeierstrassCurve K), Formalism.L2.Th1.A.IntModel W → ∀ s2 : K,
    ∀ i : ℕ, 1 ≤ i → i ≠ 2 →
      ‖jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) i‖ ≤ 1

end Formalism.L2.Th1.C
