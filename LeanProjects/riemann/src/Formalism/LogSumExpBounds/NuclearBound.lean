import Formalism.LogSumExpBounds.StatementD

namespace Formalism.NuclearRankWeightBounds.D

open Finset

def CBWeights : Prop :=
  ∀ (N : ℕ) (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian) (i : ℕ), i ≤ N →
    ∃ w : Finset (Fin N) → ℝ, (∀ J, 0 ≤ w J) ∧
      (∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J) = 1 ∧
      lead (NormedSpace.exp Y) i
        = ((∑ J ∈ powersetCard i (univ : Finset (Fin N)),
            w J * Real.exp (∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) ∧
      (∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J * (∑ j ∈ J, hY.eigenvalues j))
        = ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), (Y a a).re ∧
      (∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J * (∑ j ∈ J, hY.eigenvalues j) ^ 2)
        = (∑ a ∈ univ.filter (fun a : Fin N => a.val < i), (Y a a).re) ^ 2
          + ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
              ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2

def NuclearBound : Prop :=
  ∀ (N : ℕ) (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian),
    ∑ j, |hY.eigenvalues j| ≤ Real.sqrt (Y.rank : ℝ) * hs Y

def RankBlock : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (Y : Matrix (Fin N) (Fin N) ℂ),
    (∀ a b, ep a = ep b → Y a b = 0) → Y.rank ≤ 2 * q0 ep

def LogSumExp : Prop :=
  ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (M : ℝ),
    (∀ j, 0 ≤ w j) → ∑ j, w j = 1 → ∑ j, w j * y j = 0 → (∀ j, |y j| ≤ M) →
    min 1 M⁻¹ * (∑ j, w j * y j ^ 2) / 4 ≤ Real.log (∑ j, w j * Real.exp (y j))

def WeightedOff : Prop :=
  ∀ (N : ℕ) (s : ℕ → ℝ) (ep : Fin N → Bool) (h : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ),
    Y.IsHermitian → (∀ a b, ep a = ep b → Y a b = 0) →
    (∀ a b : Fin N, b < a → ep a ≠ ep b → h ≤ ∑ i ∈ Ico (b.val + 1) (a.val + 1), s i) →
    h * hs Y ^ 2 / 2 ≤ ∑ i ∈ Ico 1 N, s i *
      ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2

end Formalism.NuclearRankWeightBounds.D
