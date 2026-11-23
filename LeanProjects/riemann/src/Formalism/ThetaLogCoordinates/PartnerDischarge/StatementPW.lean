import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementG

namespace Formalism.InvariantFactorPaths.OddLevelGainBounds

open MvPolynomial Finset Formalism.GM.M Formalism.GM Formalism.InvariantFactorPaths.PW

noncomputable def logEightAPlusR (p : ℕ) (a : ℝ) (r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

def RealHeightBoundImplication : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (a κ : ℝ),
    1 ≤ a → (∀ x, (LL.deg x : ℝ) ≤ 2 * a) → 2 * a * N + r ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 → ((N + 2) * r ^ 2 : ℝ) * logEightAPlusR p a r ≤ κ →
    HypP p LL ρ ⌈κ / (N + 2)⌉₊ ∧ HypW p (r := r) LL ⌈κ / (N + 2)⌉₊ ∧ HypE p LL ρ ⌈κ / (N + 2)⌉₊

def LatticeTheoremOfGramBound : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    1 ≤ a → p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, ((LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x : ℝ) ≤ 2 * a) → (∀ i, (T.z i : ℝ) ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * logEightAPlusR p a r ≤ κ →
    2 * a * N + r ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      ∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * logEightAPlusR p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)

end Formalism.InvariantFactorPaths.OddLevelGainBounds
