import Mathlib
import Formalism.EllipticTorsion.Statement

open PowerSeries

universe u

namespace Formalism.ELL

open Formalism.G

def CompExpWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (σ : Type) [Finite σ] (c : ℝ),
    0 < c → c ≤ 1 →
    ∀ E : PowerSeries K, constantCoeff E = 0 →
      (∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) →
    ∀ G : MvPowerSeries σ K, IntegralMv G → ∀ α : σ →₀ ℕ,
      ‖MvPowerSeries.coeff α
          (MvPowerSeries.subst (fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) G)‖
        ≤ c ^ (-(α.degree : ℤ))

end Formalism.ELL
