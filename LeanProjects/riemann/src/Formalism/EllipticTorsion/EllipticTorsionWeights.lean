import Mathlib
import Formalism.EllipticTorsion.JetsCube

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def EllipticTorsionWeights : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 →
    ∀ (F : FormalGroup (unitBall K)) (l E g : PowerSeries K) (ζ : K),
      IsLog (FK F) l → constantCoeff E = 0 → E.subst l = X → l.subst E = X →
      (∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((p : ℝ) ^ 2 - 1))) →
      ζ ^ (p ^ 2 - 1) = 1 → (∀ m : ℕ, ¬ (p ^ 2 - 1) ∣ m → ‖ζ ^ m - 1‖ = 1) →
      IsHom (FK F) (FK F) (ζ • X) →
      constantCoeff g = 0 →
      IntegralMv (g.subst (FK F).toPowerSeries - atX g - atY g) →
      IntegralPS (g.subst (ζ • X : PowerSeries K) - ζ ^ p • g) →
      ‖coeff 1 g‖ ≤ 1 →
      ∀ n : ℕ,
        ‖coeff n (g.subst E)‖ ≤ ‖(p : K)‖ ^ (-(n : ℝ) / ((p : ℝ) ^ 2 - 1)) ∨
        (∃ j : ℕ, Odd j ∧ n = p ^ j ∧
          ‖coeff n (g.subst E)‖ ≤ ‖(p : K)‖ ^ (-1 - (n : ℝ) / ((p : ℝ) ^ 2 - 1)))

def FrobExpand : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p : ℕ), p.Prime → ‖(p : K)‖ < 1 →
    ∀ (m j : ℕ) (a b : Fin m → K), (∀ e, ‖a e‖ ≤ 1) → (∀ e, ‖a e ^ (p ^ j) - b e‖ ≤ ‖(p : K)‖) →
      ∀ α : Fin m →₀ ℕ,
        ‖MvPolynomial.coeff α
            ((∑ e, MvPolynomial.C (a e) * MvPolynomial.X e) ^ (p ^ j)
              - (∑ e, MvPolynomial.C (b e) * MvPolynomial.X e ^ (p ^ j)))‖ ≤ ‖(p : K)‖

end Formalism.ELL
