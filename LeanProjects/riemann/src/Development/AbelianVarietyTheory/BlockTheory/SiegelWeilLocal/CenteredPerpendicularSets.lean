import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

def perpSet (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ w ∈ W, Formalism.UG.hform s J w y = 0}

def IsSkew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ u u' : Fin n → A, Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') = 0

def InNil (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  IsSkew s J Y ∧ (∀ u, Y *ᵥ u ∈ perpSet s J W) ∧ (∀ u ∈ perpSet s J W, Y *ᵥ u ∈ W) ∧ ∀ u ∈ W, Y *ᵥ u = 0

def InCen (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  InNil s J W Y ∧ ∀ u ∈ perpSet s J W, Y *ᵥ u = 0

theorem inCen_zero (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) :
    InCen s J W 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [IsSkew, perpSet, Formalism.UG.hform]

end Lie

variable (I : AutInst)

def spanAt (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (R : Set _))

def nilReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def cenReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def nilInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def cenInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def diagEmb (Y : Matrix (Fin I.n) (Fin I.n) I.E) : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
  fun v => Y.map (I.φ v)

def normAt (x : I.GA) (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) : ℝ :=
  Real.sqrt (∑ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Y v * I.P v * uMat (x.1 v)))

theorem normAt_zero (x : I.GA) : normAt I x 0 = 0 := by
  simp [normAt, Formalism.REAL.hs]

def nextSize {a : ℕ} (τ : Fin a → ℝ) (i : Fin a) : ℝ :=
  if h : (i : ℕ) + 1 < a then τ ⟨(i : ℕ) + 1, h⟩ else 1 / 2

example : nextSize ![(1 : ℝ) / 8, 1 / 4] 0 = 1 / 4 ∧ nextSize ![(1 : ℝ) / 8, 1 / 4] 1 = 1 / 2 := by
  constructor <;> simp [nextSize]

def CoveringRadii : Prop :=
  ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ),
    HasFlag I x S τ → ∀ (i : Fin a) (ρ : ℝ), 0 < ρ → τ i ≤ ρ * nextSize τ i → τ i ^ 2 ≤ ρ / 4 →
      (∀ Y ∈ nilReal I (S i.succ), ∃ Y₀ ∈ nilInt I x (S i.succ), ∃ Z ∈ cenReal I (S i.succ),
        normAt I x (Y - diagEmb I Y₀ - Z) ≤
          ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * ρ / Real.sqrt (2 * I.f)) ∧
      (∀ Z ∈ cenReal I (S i.succ), ∃ Z₀ ∈ cenInt I x (S i.succ),
        normAt I x (Z - diagEmb I Z₀) ≤ ((I.n : ℝ) ^ 2 * I.f) * I.rd * ρ / (16 * Real.sqrt I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets
