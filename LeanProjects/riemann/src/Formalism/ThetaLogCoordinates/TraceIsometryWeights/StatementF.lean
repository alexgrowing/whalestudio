import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC
import Formalism.MahlerMeasure.StatementTM

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M Formalism.GM

def DischargeP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypP p LL ρ e1

def DischargeW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypW p (r := r) LL e1

def DischargeE : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypE p LL ρ e1

def HeightBoundImplication : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (a : ℕ) (κ : ℝ),
    (∀ x, LL.deg x ≤ 2 * a) → 2 * a * N + r ≤ p ^ 2 * (8 * a + r) ^ 2 → ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    HypP p LL ρ ⌈κ / (N + 2)⌉₊ ∧ HypW p (r := r) LL ⌈κ / (N + 2)⌉₊ ∧ HypE p LL ρ ⌈κ / (N + 2)⌉₊

end Formalism.InvariantFactorPaths.PW
