import Mathlib

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

def wsum {n : ℕ} (lam : Fin n → ℤ) : ℤ := ∑ i, lam i

def interl {n : ℕ} (lam : Fin (n + 1) → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i : Fin n => Finset.Icc (lam i.succ) (lam i.castSucc)

def gtChar {K : Type*} [Field K] : (n : ℕ) → (Fin n → ℤ) → (Fin n → K) → K
  | 0, _, _ => 1
  | n + 1, lam, t =>
      ∑ mu ∈ interl lam, gtChar n mu (fun i => t i.castSucc) * t (Fin.last n) ^ (wsum lam - wsum mu)

def alt {K : Type*} [Field K] (n : ℕ) (a : Fin n → ℤ) (t : Fin n → K) : K :=
  (Matrix.of fun i j : Fin n => t i ^ a j).det

def delta (n : ℕ) : Fin n → ℤ := fun j => (n : ℤ) - 1 - (j : ℤ)

def wden {K : Type*} [Field K] (n : ℕ) (t : Fin n → K) : K :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then t i - t j else 1

def WeylGTStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ t : Fin n → K, (∀ i, t i ≠ 0) →
    wden n t * gtChar n lam t = alt n (lam + delta n) t

def WdenSuccStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (t : Fin (n + 1) → K),
    wden (n + 1) t = wden n (fun i => t i.castSucc) * ∏ i : Fin n, (t i.castSucc - t (Fin.last n))

def AltBranchStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (lam : Fin (n + 1) → ℤ), Antitone lam → ∀ t : Fin (n + 1) → K, (∀ i, t i ≠ 0) →
    alt (n + 1) (lam + delta (n + 1)) t =
      (∏ i : Fin n, (t i.castSucc - t (Fin.last n))) *
        ∑ mu ∈ interl lam, alt n (mu + delta n) (fun i => t i.castSucc) * t (Fin.last n) ^ (wsum lam - wsum mu)

end ReciprocityTheory.ChartRestriction.TR.Weyl
