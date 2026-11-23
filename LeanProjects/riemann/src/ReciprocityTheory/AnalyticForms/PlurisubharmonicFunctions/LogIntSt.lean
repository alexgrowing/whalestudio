import Mathlib

namespace ReciprocityTheory.AnForm.A

open MeasureTheory

noncomputable section

def logMono {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ) : ℝ :=
  ∑ i, (m i : ℝ) * Real.log ‖z i‖

def LogNormLocIntCStatement : Prop :=
  LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume

def LogCoordLocIntStatement : Prop :=
  ∀ (D : ℕ) (i : Fin D), LocallyIntegrable (fun z : Fin D → ℂ => Real.log ‖z i‖) volume

def LogMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ), LocallyIntegrable (logMono m) volume

def LogMonoTestIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ) (f : (Fin D → ℂ) → ℝ), Continuous f → HasCompactSupport f →
    Integrable (fun z => f z * logMono m z) volume

def LogUnitMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℂ), IsOpen U →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    LocallyIntegrableOn (fun z => Real.log ‖u z * ∏ i, z i ^ m i‖) U volume

end

end ReciprocityTheory.AnForm.A
