import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalRingCardinality.DataCoeff

open scoped ComplexOrder Matrix
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum

section Defs

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {N n : ℕ}

def gramSum (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b =>
    if ha : a.1 < n then (if hb : b.1 < n then G' ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
    else (if b.1 < n then 0 else if a = Br.iL hN ∧ b = Br.iL hN then g else 0)

def normSqAt (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K) (f : VV K lam) : ℝ :=
  (s (pairK lam G f f)).re

def IsScaledCoisometry (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∃ A : VV K sg →ₗ[K] VV K lam,
    (∀ (y : VV K sg) (x : VV K lam), pairK lam G (A y) x = pairK sg G' y (P x)) ∧
    ∀ y y' : VV K sg, s (pairK lam G (A y) (A y')) = ((ρ ^ 2 : ℝ) : ℂ) * s (pairK sg G' y y')

def HasOpNormSq (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) (C : ℝ) : Prop :=
  (∀ f : VV K lam, normSqAt s sg G' (P f) ≤ C * normSqAt s lam G f) ∧
  ∃ f : VV K lam, f ≠ 0 ∧ normSqAt s sg G' (P f) = C * normSqAt s lam G f

def factor (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (T : ℝ) : ℝ :=
  T ^ (-((Br.nBr lam sg : ℤ) : ℝ) / 2) * |((Br.cBr hN lam sg : ℤ) : ℝ)| * Real.sqrt (Br.kapBr ℝ hN lam sg)

def orthNormSq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) : ℝ :=
  ∏ τ, ((Br.cBr hN (lam τ) (sg τ) : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ hN (lam τ) (sg τ)

def dOne (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w (Br.iC hN i) - lam.w (Br.iS hN i)) (Br.d0 hN lam sg)

end Defs

def LastMapNorm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (s : K →+* ℂ), (∀ x : K, s (star x) = (starRingEnd ℂ) (s x)) →
  ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
  ∀ (G' : ι → Matrix (Fin n) (Fin n) K), (∀ τ, ((G' τ).map s).PosDef) →
  ∀ (T : ℝ), 0 < T → ∀ (g t : ι → K), (∀ τ, s (star (t τ) * g τ * t τ) = (T : ℂ)) →
    (∀ τ, IsScaledCoisometry s (fun _ : Unit => lam τ) (fun _ => gramSum hN (G' τ) (g τ)) (fun _ : Unit => sg τ)
        (fun _ => G' τ) (Br.brAt hN (fun _ : Unit => lam τ) (fun _ : Unit => sg τ) fun _ => t τ)
        (factor hN (lam τ) (sg τ) T)) ∧
    IsScaledCoisometry s lam (fun τ => gramSum hN (G' τ) (g τ)) sg G' (Br.brAt hN lam sg t)
      (∏ τ, factor hN (lam τ) (sg τ) T) ∧
    HasOpNormSq s lam (fun τ => gramSum hN (G' τ) (g τ)) sg G' (Br.brAt hN lam sg t)
      (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * orthNormSq hN lam sg)

def OrthNormLogBound : Prop :=
  ∃ C : ℝ, ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
  ∀ a : ℝ, (∀ τ, (((lam τ).spread : ℤ) : ℝ) ≤ 2 * a) →
    0 < orthNormSq hN lam sg ∧
    Real.log (orthNormSq hN lam sg) ≤
      ∑ τ, (2 * ((N : ℝ) - 1) * ((dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ∧
    ∑ τ, (2 * ((N : ℝ) - 1) * ((dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ≤
      C * ∑ τ, ((N : ℝ) * ((dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) ^ 2) * Real.log (2 * a)

def LastMapNormWithBound : Prop := LastMapNorm ∧ OrthNormLogBound

section Checks

variable {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K)

theorem fockB_self_nonneg {σ : Type} (f : MvPolynomial σ ℝ) : 0 ≤ fockB f f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)

theorem factor_sq (lam : DomWeight N) (sg : DomWeight n) {T : ℝ} (hT : 0 < T) :
    factor hN lam sg T ^ 2 =
      T ^ (-Br.nBr lam sg) * (((Br.cBr hN lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ hN lam sg) := by
  have hk : 0 ≤ Br.kapBr ℝ hN lam sg := div_nonneg (fockB_self_nonneg _) (fockB_self_nonneg _)
  have h1 : (T ^ (-((Br.nBr lam sg : ℤ) : ℝ) / 2)) ^ 2 = T ^ (-Br.nBr lam sg) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  rw [factor, mul_pow, mul_pow, h1, sq_abs, Real.sq_sqrt hk, mul_assoc]

example : Br.Interlace (by rfl : 3 = 2 + 1) ⟨![3, 1, 0], by decide⟩ ⟨![2, 0], by decide⟩ ∧
    Br.SameShift (⟨![3, 1, 0], by decide⟩ : DomWeight 3) (⟨![2, 0], by decide⟩ : DomWeight 2) ∧
    Br.nBr (⟨![3, 1, 0], by decide⟩ : DomWeight 3) (⟨![2, 0], by decide⟩ : DomWeight 2) = 2 ∧
    dOne (by rfl : 3 = 2 + 1) ⟨![3, 1, 0], by decide⟩ ⟨![2, 0], by decide⟩ = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Br.Interlace; decide
  · unfold Br.SameShift; decide
  · decide
  · decide

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum
