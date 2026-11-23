import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

def stdForm (K : Type) [Field K] [StarRing K] (M : ℕ) : (Fin M → K) →ₗ⋆[K] (Fin M → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (by intro x x' y; simp [add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (by intro x y y'; simp [mul_add, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring))

def stdLat (K : Type) [Field K] [NumberField K] (M : ℕ) : Submodule (𝓞 K) (Fin M → K) :=
  Submodule.span (𝓞 K) (Set.range (fun i : Fin M => (Pi.single i 1 : Fin M → K)))

def massI (D : D7) (M : ℕ) : ℝ :=
  letI := D.host.cmStar
  Formalism.HermitianLatticesTheory.mass (stdForm D.host.E M) (stdLat D.host.E M)

def zetaR (M : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M

def vand {N : ℕ} (x : Fin N → ℝ) : ℝ := ∏ a : Fin N, ∏ b ∈ univ.filter (fun b => a < b), (x a - x b)

def facProd (N : ℕ) : ℝ := ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

def dimV {N : ℕ} (x : Fin N → ℝ) : ℝ := vand x / facProd N

def rhoN {N : ℕ} (s : Fin N → Bool) (c : Fin N) : ℝ :=
  (((univ.filter (fun b => c < b ∧ s b ≠ s c)).card : ℝ) -
    ((univ.filter (fun a => a < c ∧ s a ≠ s c)).card : ℝ)) / 2

def nPlus {N : ℕ} (s : Fin N → Bool) : ℕ := (univ.filter (fun a => s a = true)).card

def nMinus {N : ℕ} (s : Fin N → Bool) : ℕ := (univ.filter (fun a => s a = false)).card

def dTau {N : ℕ} (s : Fin N → Bool) (lam : Fin N → ℝ) : ℝ :=
  (∏ a : Fin N, ∏ b ∈ univ.filter (fun b => a < b ∧ s a = s b),
      ((lam a + rhoN s a) - (lam b + rhoN s b))) /
    (facProd (nPlus s) * facProd (nMinus s))

def lamAbs {N : ℕ} (lam : Fin N → ℝ) : ℝ := ⨆ a : Fin N, ⨆ b : Fin N, |lam a - lam b|

def GapAtLeast {N : ℕ} (s : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ) : Prop :=
  ∀ a b : Fin N, s a ≠ s b → h ≤ |lam a - lam b|

def rowLam (D : D7) (ρ : D.what₂.Tau) : Fin (D.R.k - 1 + D.R.m) → ℝ :=
  Fin.append (fun i => (((D.hc ρ).v i : ℚ) : ℝ)) (fun j => -(((D.hc ρ).b j : ℚ) : ℝ))

def rowSgn (D : D7) : Fin (D.R.k - 1 + D.R.m) → Bool :=
  Fin.append (fun _ => true) (fun j : Fin D.R.m => decide (j.val % 2 = 0))

def IsUnitri {n : ℕ} {F : Type} [Zero F] [One F] (A : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1

def blk (rS k i : ℕ) : ℕ := if i < rS then i else if i < rS + k + 1 then rS else i - k

def IsRowLev (k rS : ℕ) {n : ℕ} {F : Type} [Zero F] [One F] (A : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j : Fin n, blk rS k j.val < blk rS k i.val → A i j = 0) ∧ (∀ i, A i i = 1) ∧
  (∀ i j : Fin n, blk rS k i.val = blk rS k j.val → j < i → A i j = 0) ∧
  (∀ i j : Fin n, j.val = rS + k → i ≠ j → blk rS k i.val = rS → A i j = 0)

def idxLoc (F : Type) [CommRing F] (n : ℕ) (P : Matrix (Fin n) (Fin n) F → Prop) : ℝ :=
  (Nat.card (GL (Fin n) F) : ℝ) / (Nat.card {A : GL (Fin n) F // P (A : Matrix (Fin n) (Fin n) F)} : ℝ)

def idxColLoc (g k : ℕ) : ℝ := idxLoc (ZMod g) k IsUnitri

def idxRowLoc (g k m : ℕ) : ℝ := idxLoc (ZMod g) (k + m - 1) (IsRowLev k (m / 2 - 1))

def idxPi (D : D7) (g₁ g₂ : ℕ) : ℝ := idxColLoc g₁ D.R.k ^ D.R.f * idxColLoc g₂ D.R.k ^ D.R.f

def idxSig (D : D7) (g₁ g₂ : ℕ) : ℝ :=
  idxRowLoc g₁ D.R.k D.R.m ^ D.R.f * idxRowLoc g₂ D.R.k D.R.m ^ D.R.f

def dimN (k m : ℕ) : ℕ :=
  ((range (k + m - 1) ×ˢ range (k + m - 1)).filter
    (fun p : ℕ × ℕ => p.1 < p.2 ∧ blk (m / 2 - 1) k p.1 ≠ blk (m / 2 - 1) k p.2)).card

def duStarP (D : D7) (g₁ g₂ : ℕ) (uc : D.what₂.Tau → Fin D.R.k → ℝ) : ℝ :=
  massI D D.R.k * idxPi D g₁ g₂ * ∏ ρ, dimV (uc ρ)

def DstarP (D : D7) (g₁ g₂ : ℕ) (volY0 : ℝ) (dsig : D.what₂.Tau → ℝ) : ℝ :=
  volY0 * idxSig D g₁ g₂ * ∏ ρ, dsig ρ

def logXu (D : D7) (Dst dst : ℝ) : ℝ := (1 / ((D.R.f : ℝ) * D.R.k)) * Real.log (Dst / dst)

def volY0 (D : D7) : ℝ := letI := D.host.cmStar; D.vol (D.sp.Y 0)

def uColR (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) : Fin D.R.k → ℝ :=
  fun i => (((D.hcW u ρ).u i : ℚ) : ℝ)

def duStarU (D : D7) (u : D.what₂.Word) : ℝ := duStarP D (D.host.g 0) (D.host.g 1) (uColR D u)

def DstarD (D : D7) : ℝ := DstarP D (D.host.g 0) (D.host.g 1) (volY0 D) D.dsig

def logXuD (D : D7) (u : D.what₂.Word) : ℝ := logXu D (DstarD D) (duStarU D u)

end Formalism.MainNotions.StandardLattice
