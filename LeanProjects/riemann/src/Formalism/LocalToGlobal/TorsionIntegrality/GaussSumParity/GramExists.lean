import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementC

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

def EigenOdd : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l → ∀ (ι : Type) [Fintype ι]
    (om oms : ι → K) (b : K) (c : ι → ι → K), (∀ r r', σ (σ (c r' r)) = c r' r) →
    (∀ r, b * oms r = ∑ r', σ (c r' r) * oms r') → ∀ s : ZMod d, s.val % 2 = 1 →
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (c x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] b) * zXY l σ om oms s

def GramExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → (∃ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1)) →
    ∀ (E : Type) [Fintype E] [DecidableEq E],
      ∃ c : Bool × E → Bool × E → K,
        (∀ k x, ‖c k x‖ ≤ 1 ∧ σ (σ (c k x)) = c k x) ∧
        ∀ x x' : Bool × E, ∑ k, c k x * σ (c k x') = if x.1 ≠ x'.1 ∧ x.2 = x'.2 then 1 else 0

end Formalism.L2.Th1.D
