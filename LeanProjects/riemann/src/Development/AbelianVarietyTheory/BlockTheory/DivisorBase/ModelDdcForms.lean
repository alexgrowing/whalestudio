import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def formAt (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (P : LocPot X) (z w : Fin e → ℂ) : ℝ :=
  2 / Real.pi * levi (P.φ (ψ.symm z) ∘ ψ.symm) z w

def ddcAt (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (f : X → ℝ) (z w : Fin e → ℂ) : ℝ :=
  1 / Real.pi * levi (f ∘ ψ.symm) z w

def gradSqAt (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (f : X → ℝ) (z w : Fin e → ℂ) : ℝ :=
  1 / Real.pi *
    (((fderiv ℝ (f ∘ ψ.symm) z w) ^ 2 + (fderiv ℝ (f ∘ ψ.symm) z (Complex.I • w)) ^ 2) / 4)

def normSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  ‖s y y‖ * Real.exp (-L.φ y y)

variable {m : ℕ}

def IsBoundary (A : FinHolAtlas e X) (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ)
    (D : Fin m → Set X) : Prop :=
  ∀ i, IsPotential A (L i) ∧ IsSection A (L i) (s i) ∧
    IsSNC A (L i) (s i) (Pi.single i 1) D ∧ ∀ y, normSec (L i) (s i) y ≤ 1

def rComp (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (i : Fin m) (y : X) : ℝ :=
  Real.exp 1 - Real.log (normSec (L i) (s i) y ^ 2)

def rTot (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (y : X) : ℝ :=
  Real.exp 1 - Real.log ((∏ i, normSec (L i) (s i) y) ^ 2)

def poincarePot (K : LocPot X) (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (c : ℝ) :
    LocPot X :=
  K + LocPot.ofFun fun y => -(c / 2) * ∑ i, Real.log (rComp L s i y)

def IsPotentialOn (A : FinHolAtlas e X) (O : Set X) (P : LocPot X) : Prop :=
  (∀ x, A.SmoothOn (P.U x ∩ O) (P.φ x)) ∧
  ∀ x x', ∀ y ∈ P.U x ∩ P.U x' ∩ O, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
    A.HoloOn W G ∧ ∀ z ∈ W ∩ P.U x ∩ P.U x' ∩ O, P.φ x z - P.φ x' z = (G z).re

def IsAdaptedPolydisc (A : FinHolAtlas e X) (D : Fin m → Set X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)) : Prop :=
  IsCompatChart A ψ ∧ Metric.ball (0 : Fin e → ℂ) 1 ⊆ ψ.target ∧
    (∀ i i' k, σ i = some k → σ i' = some k → i = i') ∧
    ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, ∀ i, ψ.symm z ∈ D i ↔ ∃ k, σ i = some k ∧ z k = 0

def tOf (z : ℂ) : ℝ := -Real.log ‖z‖ / (2 * Real.pi)

open scoped Classical in

def modelAt (σ : Fin m → Option (Fin e)) (z w : Fin e → ℂ) : ℝ :=
  ∑ k, if ∃ i, σ i = some k then ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2) else ‖w k‖ ^ 2

open scoped Classical in

def tSum (σ : Fin m → Option (Fin e)) (z : Fin e → ℂ) : ℝ :=
  1 + ∑ k, if ∃ i, σ i = some k then tOf (z k) else 0

def ScalarBounds (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) : Prop :=
  ∀ y, y ∉ ⋃ i, D i →
    (∀ i, Real.exp 1 ≤ rComp L s i y) ∧
    rTot L s y = ∑ i, rComp L s i y - ((m : ℝ) - 1) * Real.exp 1 ∧
    (∀ i, rComp L s i y ≤ rTot L s y) ∧
    (1 ≤ m → Real.log (rTot L s y) ≤ ∑ i, Real.log (rComp L s i y) ∧
      ∑ i, Real.log (rComp L s i y) ≤ m * Real.log (rTot L s y))

def TwoSided (A : FinHolAtlas e X) (K : LocPot X) (L : Fin m → LocPot X)
    (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (c : ℝ) : Prop :=
  ∀ ψ, IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ i, D i → ∀ w,
    formAt ψ K z w / 2 + c * ∑ i, gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2
        ≤ formAt ψ (poincarePot K L s c) z w ∧
    formAt ψ (poincarePot K L s c) z w
        ≤ 2 * formAt ψ K z w
          + c * ∑ i, gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2

def GrowthBounds (A : FinHolAtlas e X) (K : LocPot X) (L : Fin m → LocPot X)
    (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (c C : ℝ) : Prop :=
  ∀ ψ, IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ i, D i → ∀ w,
    gradSqAt ψ (rTot L s) z w / rTot L s (ψ.symm z) ^ 2 ≤ C * formAt ψ (poincarePot K L s c) z w ∧
    |ddcAt ψ (fun y => Real.log (rTot L s y)) z w| ≤ C * formAt ψ (poincarePot K L s c) z w ∧
    |ddcAt ψ (rTot L s) z w| ≤ C * formAt ψ K z w ∧
    formAt ψ (poincarePot K L s c) z w ≤ C * Real.exp (rTot L s (ψ.symm z)) * formAt ψ K z w

end

def PoincareFormStatement : Prop :=
  ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X)
    (K : LocPot X), IsPotential A K → IsPosPot A K →
    ∀ (m : ℕ) (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X),
      IsBoundary A L s D →
      ∃ cs : ℝ, 0 < cs ∧
        IsOpen (⋃ i, D i)ᶜ ∧
        ScalarBounds L s D ∧
        (∀ c : ℝ, 0 < c → c ≤ cs →
          IsPotentialOn A (⋃ i, D i)ᶜ (poincarePot K L s c) ∧
          TwoSided A K L s D c ∧
          (∃ C : ℝ, 0 < C ∧ GrowthBounds A K L s D c C) ∧
          maMeasure A (fun _ => poincarePot K L s c) (⋃ i, D i)ᶜ < ⊤) ∧
        ∀ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)),
          IsAdaptedPolydisc A D ψ σ →
          ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧
            (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i →
              C⁻¹ * tSum σ z ≤ rTot L s (ψ.symm z) ∧ rTot L s (ψ.symm z) ≤ C * tSum σ z) ∧
            ∀ c : ℝ, 0 < c → c ≤ cs →
              ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i → ∀ w,
                C⁻¹ * modelAt σ z w ≤ formAt ψ (poincarePot K L s c) z w ∧
                formAt ψ (poincarePot K L s c) z w ≤ C * modelAt σ z w

theorem gradSqAt_nonneg {e : ℕ} {X : Type} [TopologicalSpace X]
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (f : X → ℝ) (z w : Fin e → ℂ) :
    0 ≤ gradSqAt ψ f z w := by
  unfold gradSqAt
  have := Real.pi_pos
  positivity

theorem rComp_eq {X : Type} [TopologicalSpace X] {m : ℕ} (L : Fin m → LocPot X)
    (s : Fin m → X → X → ℂ) (i : Fin m) (y : X) :
    rComp L s i y = Real.exp 1 - 2 * logNormSec (L i) (s i) y := by
  simp [rComp, normSec, logNormSec, Real.log_pow]

theorem rTot_zero {X : Type} [TopologicalSpace X] (L : Fin 0 → LocPot X)
    (s : Fin 0 → X → X → ℂ) (y : X) : rTot L s y = Real.exp 1 := by
  simp [rTot]

end GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms
