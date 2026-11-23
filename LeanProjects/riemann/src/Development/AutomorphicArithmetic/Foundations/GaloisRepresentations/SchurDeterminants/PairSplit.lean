import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

def MixDet : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (d d' : Fin n → R),
    ∑ i, (Matrix.of fun a j : Fin n => (if j = i then d a else d' a) * M a j).det =
      (∑ a, d a * ∏ b ∈ univ.erase a, d' b) * M.det

def vdmAway {R : Type} [CommRing R] {n : ℕ} (i : Fin n) (g : Fin n → R) : R :=
  ∏ a ∈ univ.erase i, ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b)

def PairSplit : Prop :=
  ∀ (R : Type) [CommMonoid R] (n : ℕ) (F : Fin n → Fin n → R) (i : Fin n),
    ∏ a, ∏ b ∈ Finset.Ioi a, F a b =
      (∏ a ∈ univ.erase i, ∏ b ∈ (Finset.Ioi a).erase i, F a b) *
        ∏ k ∈ univ.erase i, (if k < i then F k i else F i k)

def VdmSplit : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (g : Fin n → R) (i : Fin n),
    vdm g = (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - g k)

def PairCount : Prop :=
  ∀ (n : ℕ) (i : Fin n),
    ∑ k ∈ univ.erase i, (n - 1 - (k : ℕ)) = (n - 1).choose 2 + (i : ℕ) ∧
    ∑ a ∈ univ.erase i, ((Finset.Ioi a).erase i).card = (n - 1).choose 2

def OffClrRed : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    ∑ i, sch lam (scaleOff y i g) * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))

def OffClrPow : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    y ^ (n - 1).choose 2 *
      ∑ i, sch lam (scaleOff y i g) * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      y ^ (n - 1).choose 2 * (sch lam g * vdm g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)))

def Expand : Prop :=
  ∀ (K R π : Type) [CommRing K] [CommRing R] [Algebra K R] [Fintype π] [DecidableEq π] (n : ℕ) (x : π → R)
    (g : π → Fin n → R),
    ∏ p, detOne (x p) (g p) =
      ∑ m : π → Fin (n + 1), (∏ p, x p ^ (m p : ℕ)) *
        ∏ p, ((-1) ^ (m p : ℕ) * aeval (g p) (esymm (Fin n) K (m p)))

def DenseSub : Prop :=
  ∀ (K σ : Type) [Field K] [CharZero K] [Fintype σ] (L : AddSubgroup (σ → K)) (a : σ → K),
    Submodule.span K (L : Set (σ → K)) = ⊤ → ZDense {x | x - a ∈ L}

def SpanTop : Prop :=
  ∀ (O K ι : Type) [CommRing O] [Field K] [Fintype ι] (τ : ι → (O →+* K)), Function.Injective τ →
    ∀ (N : O), (∀ t, τ t N ≠ 0) → ∀ k : ℕ,
      Submodule.span K {x : ι × Fin k → K | ∃ β : Fin k → O, x = pt τ (fun s => N * β s)} = ⊤

def DenseOff : Prop :=
  ∀ (K σ : Type) [Field K] (D : Set (σ → K)), ZDense D → ∀ Q : MvPolynomial σ K, Q ≠ 0 →
    ZDense {x | x ∈ D ∧ eval x Q ≠ 0}

def SpanProd : Prop :=
  ∀ (K ι : Type) [CommRing K] [Fintype ι] [DecidableEq ι] (n : ℕ) (P : ι → MvPolynomial (Fin n) K),
    (∀ t, (P t).IsSymmetric) → ∃ k₀, ∀ k, k₀ ≤ k → ∃ w : (ι × Fin k → Fin (n + 1)) → K,
      ∀ (R : Type) [CommRing R] [Algebra K R] (g : ι → Fin n → R),
        ∏ t, aeval (g t) (P t) =
          ∑ m, w m • ∏ p : ι × Fin k, ((-1) ^ (m p : ℕ) * aeval (g p.1) (esymm (Fin n) K (m p)))

def eSpan (K : Type) [CommRing K] (n k : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (Set.range fun m : Fin k → Fin (n + 1) => ∏ s, esymm (Fin n) K (m s))

def ESpanMul : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ),
    (∀ k l, k ≤ l → eSpan K n k ≤ eSpan K n l) ∧
    (∀ k l P Q, P ∈ eSpan K n k → Q ∈ eSpan K n l → P * Q ∈ eSpan K n (k + l))

end UpperTheory.Gal.Schur
