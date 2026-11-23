import Mathlib

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace PI.EllRegPr

variable {d : ℕ}

def pdc : List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pdc w u) x (Pi.single i 1)

structure DOp (d : ℕ) where
  ord : ℕ
  a : (k : Fin (ord + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ

def DOp.tr (A : DOp d) (ψ : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (A.ord + 1), ∑ w : Fin k → Fin d,
    (-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => A.a k w y * ψ y) x

def DOp.symb (A : DOp d) (x ξ : Fin d → ℝ) : ℂ :=
  ∑ w : Fin A.ord → Fin d, (∏ i, (ξ (w i) : ℂ)) * A.a (Fin.last A.ord) w x

def DOp.SmoothOn (A : DOp d) (X : Set (Fin d → ℝ)) : Prop := ∀ k w, ContDiffOn ℝ ∞ (A.a k w) X

def DOp.EllipticOn (A : DOp d) (X : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → A.symb x ξ ≠ 0

def DOp.charSet (A : DOp d) (X : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | p.1 ∈ X ∧ p.2 ≠ 0 ∧ A.symb p.1 p.2 = 0}

def IsTest (X : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ X

def distOf (u : (Fin d → ℝ) → ℂ) : ((Fin d → ℝ) → ℂ) → ℂ := fun ψ => ∫ x, u x * ψ x

def distApp (A : DOp d) (u : (Fin d → ℝ) → ℂ) : ((Fin d → ℝ) → ℂ) → ℂ := fun ψ => ∫ x, u x * A.tr ψ x

def ftD (T : ((Fin d → ℝ) → ℂ) → ℂ) (φ : (Fin d → ℝ) → ℂ) (ξ : Fin d → ℝ) : ℂ :=
  T (fun x => φ x * Complex.exp (-(Complex.I * ((x ⬝ᵥ ξ : ℝ) : ℂ))))

def wt (s : ℝ) (ξ : Fin d → ℝ) : ℝ := (1 + ξ ⬝ᵥ ξ) ^ s

def WFs (s : ℝ) (T : ((Fin d → ℝ) → ℂ) → ℂ) (X : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | p.1 ∈ X ∧ p.2 ≠ 0 ∧ ¬ ∃ (φ : (Fin d → ℝ) → ℂ) (Γ : Set (Fin d → ℝ)), IsTest X φ ∧ φ p.1 ≠ 0 ∧
    IsOpen Γ ∧ p.2 ∈ Γ ∧ (∀ η ∈ Γ, η ≠ 0) ∧ (∀ η ∈ Γ, ∀ t : ℝ, 0 < t → t • η ∈ Γ) ∧
    (∫⁻ ξ in Γ, ENNReal.ofReal (wt s ξ * Complex.normSq (ftD T φ ξ))) < ⊤}

def HsLoc (s : ℝ) (T : ((Fin d → ℝ) → ℂ) → ℂ) (X : Set (Fin d → ℝ)) : Prop :=
  ∀ φ, IsTest X φ → (∫⁻ ξ, ENNReal.ofReal (wt s ξ * Complex.normSq (ftD T φ ξ))) < ⊤

def WFsEmptyIff : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (s : ℝ), IsOpen X → ContinuousOn u X →
    (WFs s (distOf u) X = ∅ ↔ HsLoc s (distOf u) X)

def WFsChar : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (A : DOp d) (s : ℝ), IsOpen X → ContinuousOn u X →
    A.SmoothOn X → HsLoc s (distApp A u) X → WFs (s + A.ord) (distOf u) X ⊆ A.charSet X

def WFsElliptic : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (A : DOp d) (s : ℝ), IsOpen X → ContinuousOn u X →
    A.SmoothOn X → A.EllipticOn X → WFs (s - A.ord) (distApp A u) X = WFs s (distOf u) X

end PI.EllRegPr

namespace PI

def EllipticRegularity2 : Prop := EllRegPr.WFsEmptyIff ∧ EllRegPr.WFsChar ∧ EllRegPr.WFsElliptic

end PI
