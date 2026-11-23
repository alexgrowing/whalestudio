import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def DN (ε : Fin m → Bool) (t : ℝ) (h : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  C (Complex.I * t) * (∑ i, ∑ j, C (h i j) * Qp ε j i) * R

def eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) * pderiv (a, j, false) R +
    (∑ i, X (a, i, true) * C (star (H i j))) * pderiv (a, j, true) R)

def DM (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  C ((m : ℂ) * H.trace) * R + eulH H R -
    C (2 * (c : ℂ)) * (∑ i, ∑ j, C (H i j) * (Qb ε true j i + Qb ε false j i)) * R

def SecDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n),
    R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) → ∀ (y : GR n)
    (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian →
    (∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL (DN ε t H R) ((k : GR n) * y)‖ ≤ δ) ∧
    (∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL (DM ε c H R) ((k : GR n) * y)‖ ≤ δ)

end PositivityTheory.Rg.Sw.AbsSt
