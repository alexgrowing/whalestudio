import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

def UnitCols : Prop :=
  ∀ (n l : ℕ), l ≤ n → ∀ I : Fin (n - l) → Fin n, Function.Injective I →
    ∃ (J : Fin l → Fin n) (ε : ℤ), Function.Injective J ∧ (∀ i q, J i ≠ I q) ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ (A : Type) [CommRing A] (z : Fin n → ℕ → A),
        (catM l (unitM A I) z).det = (ε : A) * (Matrix.of fun i i' : Fin l => z (J i') i.val).det

def UnitColsZero : Prop :=
  ∀ (n l : ℕ), l ≤ n → ∀ I : Fin (n - l) → Fin n, ¬ Function.Injective I →
    ∀ (A : Type) [CommRing A], (∀ z : Fin n → ℕ → A, (catM l (unitM A I) z).det = 0) ∧
      initMinor A (n := n) I (Nat.sub_le n l) = 0

def MinorZero : Prop :=
  ∀ (A : Type) [CommRing A] (r n s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r), ¬ Function.Injective I → initMinor A I hs = 0

def HvFull : Prop :=
  ∀ (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c e : ℕ, (∀ t, μ t ≤ c) → (∀ t, e ≤ μ t) →
    (∀ t : Fin n, t.val + 1 = n → μ t = e) → 0 < n →
    ∀ (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A),
      hvE x y c (fun k => colH μ k.val) (fun k => colH_le μ k.val) =
        ((Matrix.of fun a i : Fin n => x a i.val).det * y.det) ^ e *
          hvE x y c (fun k => colH (fun t => μ t - e) k.val) (fun k => colH_le _ k.val)

def HvMemE : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ c : ℕ, (∀ t, ν t ≤ c) → ∀ x : Fin n → ℕ → K,
    hvE (fun a i => C (x a i)) (yV K n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val) ∈ dualWeyl K n n ν

def HvMemO : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c : ℕ, (∀ t, μ t ≤ c) → ∀ x : Fin n → ℕ → K,
    hvO (fun a i => C (x a i)) (yV K n) c (fun k => colH μ k.val) ∈ dualWeyl K n n fun t => c - μ t.rev

end Formalism.L2.PairingIndexBounds.Ent
