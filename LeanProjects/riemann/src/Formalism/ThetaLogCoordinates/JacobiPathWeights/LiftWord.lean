import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DefsCol

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {ι : Type*}

def stepQ (p : ℕ) (lt : ℕ → ι) (s : ι → ℤ) (l : ℕ) : ℕ :=
  if l = 0 then 1 else p ^ (s (lt l) - s (lt (l - 1))).toNat

def lastQ (p : ℕ) (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ) : ℕ :=
  if L = 0 then 1 else p ^ (z - s (lt (L - 1))).toNat

def levP (p : ℕ) (s : ι → ℤ) (z : ℤ) (i : ι) : ℕ := p ^ (z - s i).toNat

def liftWord {R : Type*} [CommRing R] {n : ℕ} (p : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (s : ι → ℤ) (X : ι → Fin n → R) : ℕ → Form R n
  | 0 => oneF
  | l + 1 => stepF (colUp primal isVec lt l) (powF (liftWord p primal isVec lt s X l) (stepQ p lt s l))
      (X (lt l))

def liftCol {R : Type*} [CommRing R] {n : ℕ} (p : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (s : ι → ℤ) (z : ℤ) (X : ι → Fin n → R) (L : ℕ) : Form R n :=
  powF (liftWord p primal isVec lt s X L) (lastQ p lt s z L)

def nomOrd (p r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (s : ι → ℤ) : ℕ → ℕ
  | 0 => 0
  | l + 1 => stepQ p lt s l * nomOrd p r primal isVec lt s l +
      (if colCostly r primal isVec lt l then 1 else 0)

def nomOrdC (p r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ) : ℕ :=
  lastQ p lt s z L * nomOrd p r primal isVec lt s L

def PosHyp (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ) : Prop :=
  (∀ l, l + 1 < L → s (lt l) ≤ s (lt (l + 1))) ∧ (∀ l < L, s (lt l) ≤ z) ∧
    ∀ l, l + 1 < L → colCostly r primal isVec lt (l + 1) → s (lt l) < s (lt (l + 1))

def minorF {R : Type*} [CommRing R] {n : ℕ} (m : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    (m.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det
  else 0

def actF {R : Type*} [CommRing R] {n : ℕ} (K : Form R n) (m : Matrix (Fin n) (Fin n) R) : Form R n :=
  fun J => ∑ I : Finset (Fin n), K I * minorF m I J

def heavy (r K : ℕ) (isVec : ι → Bool) (x : ι × Fin (r + K)) : Prop := isVec x.1 = true ↔ r ≤ x.2.val

instance (r K : ℕ) (isVec : ι → Bool) (x : ι × Fin (r + K)) : Decidable (heavy r K isVec x) := by
  unfold heavy; infer_instance

def planeRow {O : Type*} [CommRing O] (r K : ℕ) (isVec : ι → Bool) (w : O) (i : ι) :
    Fin (r + K) → MvPolynomial (ι × Fin (r + K)) O :=
  fun a => if heavy r K isVec (i, a) then C w * X (i, a) else X (i, a)

def planeEmb {O : Type*} [CommRing O] (r K : ℕ) (isVec : ι → Bool) (w : O) :
    MvPolynomial (ι × Fin (r + K)) O →ₐ[O] MvPolynomial (ι × Fin (r + K)) O :=
  aeval fun x => planeRow r K isVec w x.1 x.2

def heavyDeg (r K : ℕ) (isVec : ι → Bool) (e : ι × Fin (r + K) →₀ ℕ) : ℕ :=
  e.sum fun x d => if heavy r K isVec x then d else 0

def sigM {W O : Type*} [CommRing W] [CommRing O] [Algebra W O] {τ : Type*} {n : ℕ} (σ : RingAut W) (s : ℤ)
    (m : Matrix (Fin n) (Fin n) W) : Matrix (Fin n) (Fin n) (MvPolynomial τ O) :=
  m.map fun a => C (algebraMap W O ((σ ^ s) a))

def frameRow {W O : Type*} [CommRing W] [CommRing O] [Algebra W O] (r K : ℕ) (isVec : ι → Bool) (w : O)
    (σ : RingAut W) (s : ι → ℤ) (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ) (i : ι) :
    Fin (r + K) → MvPolynomial (ι × Fin (r + K)) O :=
  if isVec i then Matrix.vecMul (planeRow r K isVec w i) (sigM σ (s i) (↑h⁻¹ : Matrix _ _ W))
  else Matrix.vecMul (planeRow r K isVec w i) (sigM σ (s i) (↑h : Matrix _ _ W)).transpose

def frameM {W O : Type*} [CommRing W] [CommRing O] [Algebra W O] (r K : ℕ) (primal : Bool) (lt : ℕ → ι)
    (σ : RingAut W) (s : ι → ℤ) (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ) (l : ℕ) :
    Matrix (Fin (r + K)) (Fin (r + K)) (MvPolynomial (ι × Fin (r + K)) O) :=
  if primal then sigM σ (s (lt (l - 1))) (↑h : Matrix _ _ W)
  else (sigM σ (s (lt (l - 1))) (↑h⁻¹ : Matrix _ _ W)).transpose

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
