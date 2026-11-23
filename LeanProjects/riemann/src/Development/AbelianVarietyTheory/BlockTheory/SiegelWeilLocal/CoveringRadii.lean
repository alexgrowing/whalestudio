import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NilpotentCenteredRadii

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

def InNil (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  Formalism.UG.cT s Y * J + J * Y = 0 ∧
    (∀ y, ∀ w ∈ W, Formalism.UG.hform s J w (Y *ᵥ y) = 0) ∧
    (∀ y, (∀ w ∈ W, Formalism.UG.hform s J w y = 0) → Y *ᵥ y ∈ W) ∧
    ∀ w ∈ W, Y *ᵥ w = 0

def InCen (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  InNil s J W Y ∧ ∀ y, (∀ w ∈ W, Formalism.UG.hform s J w y = 0) → Y *ᵥ y = 0

example (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) :
    InCen s J W 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have : Formalism.UG.cT s (0 : Matrix (Fin n) (Fin n) A) = 0 := by
      ext i j; simp [Formalism.UG.cT]
    simp [this]
  · intro y w _; simp [Formalism.UG.hform]
  · intro y _; simp
  · intro w _; simp
  · intro y _; simp

end Lie

variable (I : AutInst)

def spanE (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Submodule I.E (Fin I.n → I.E) :=
  Submodule.span I.E (R : Set (Fin I.n → I.E))

def spanAt (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (R : Set (Fin I.n → I.E)))

def nilR (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def cenR (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def nilO (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InNil (starRingEnd I.E) I.J (spanE I R) Y ∧ ∀ y ∈ lamX I x, Y *ᵥ y ∈ lamX I x}

def cenO (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InCen (starRingEnd I.E) I.J (spanE I R) Y ∧ ∀ y ∈ lamX I x, Y *ᵥ y ∈ lamX I x}

def diagR (Y : Matrix (Fin I.n) (Fin I.n) I.E) : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
  fun v => Y.map (I.φ v)

def normX (x : I.GA) (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) : ℝ :=
  Real.sqrt (∑ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Y v * I.P v * uMat (x.1 v)))

def nextSize {a : ℕ} (τ : Fin a → ℝ) (i : Fin a) : ℝ :=
  if h : (i : ℕ) + 1 < a then τ ⟨(i : ℕ) + 1, h⟩ else 1 / 2

example (τ : Fin 1 → ℝ) : nextSize τ 0 = 1 / 2 := by simp [nextSize]

example (τ : Fin 2 → ℝ) : nextSize τ 0 = τ 1 := by simp [nextSize]

def CoveringRadii : Prop :=
  ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ),
    HasFlag I x S τ → ∀ (i : Fin a) (ρ : ℝ), 0 < ρ → τ i ≤ ρ * nextSize τ i → τ i ^ 2 ≤ ρ / 4 →
      (∀ Y ∈ nilR I (S i.succ), ∃ Y₀ ∈ nilO I x (S i.succ), ∃ Z ∈ cenR I (S i.succ),
        normX I x (Y - diagR I Y₀ - Z) ≤
          ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * ρ / Real.sqrt (2 * I.f)) ∧
      (∀ Z ∈ cenR I (S i.succ), ∃ Z₀ ∈ cenO I x (S i.succ),
        normX I x (Z - diagR I Z₀) ≤
          ((I.n : ℝ) ^ 2 * I.f) * I.rd * ρ / (16 * Real.sqrt I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.NilpotentCenteredRadii
