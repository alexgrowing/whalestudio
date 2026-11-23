import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensLeibniz.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (f g : (Fin (D + 1) → ℂ) → ℝ) (z : Fin (D + 1) → ℂ),
    ContDiffAt ℝ 2 f z → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (fun y => f y * g y) φ) z =
          f z * maDens (Fin.cons g φ) z + g z * maDens (Fin.cons f φ) z + gradDens φ f g z +
            gradDens φ g f z ∧
        maDens (Fin.cons (fun y => f y ^ 2 / 2) φ) z =
          f z * maDens (Fin.cons f φ) z + gradDens φ f f z

def EnergyDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (v : (Fin (d + 1) → ℂ) → ℝ),
    AnalyticAt ℂ s y → 0 ≤ gradDens (fun _ : Fin d => euclPot ∘ s) v v y

def GradDensSheetBound.Statement : Prop :=
  ∀ (n d : ℕ) (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ)),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ)
        (v w : (Fin (d + 1) → ℂ) → ℝ), AnalyticAt ℂ s y → s y ∈ K →
          |gradDens (fun i => φ i ∘ s) v w y| ≤
            C * Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) v v y) *
              Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) w w y)

end

end GroundTheory.Heights₂.Heights
