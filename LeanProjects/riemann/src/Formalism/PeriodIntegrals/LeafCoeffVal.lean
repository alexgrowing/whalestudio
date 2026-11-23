import Mathlib

noncomputable section

namespace PI

open Finset

def posSub {n' : ℕ} (s : Fin n') (d : ℕ) : Fin n' :=
  ⟨(s.val + n' * d - d) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

def posAdd {n' : ℕ} (s : Fin n') (e : ℕ) : Fin n' :=
  ⟨(s.val + e) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

def IsLeaf (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) : Prop :=
  (∀ i, PowerSeries.constantCoeff (t i) = 0) ∧
  ∀ (i : Fin h) (n : ℕ), ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (posSub i k)) ^ (p ^ (2 * k))) / (p : K) ^ k =
    if i.val = 0 ∧ n = 1 then 1 else 0

def ze3 (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) (i1 : Fin h) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (posSub i1 k)) ^ (p ^ (2 * k + 1))) / (p : K) ^ (k + 1)

def LeafCoeffVal : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (i0 : Fin 1) (t : Fin 1 → PowerSeries ℚ), IsLeaf p t → ∀ e : ℕ,
    padicValRat p (PowerSeries.coeff (p ^ 3 * p ^ e) ((-ze3 p t (posAdd i0 1)) ^ (p ^ e)) / ((p ^ e).factorial : ℚ)) =
      -(((p : ℤ) + 1) * (p : ℤ) ^ e + padicValNat p (p ^ e).factorial)

end PI

end
