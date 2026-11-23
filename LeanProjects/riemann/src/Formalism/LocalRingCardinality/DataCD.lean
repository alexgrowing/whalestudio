import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.BasicNotions

open MeasureTheory Filter Topology Matrix

def UpqT (P Q : ℕ) : Type := Formalism.UG.Upq P Q

instance (P Q : ℕ) : Group (UpqT P Q) := inferInstanceAs (Group (Formalism.UG.Upq P Q))
instance (P Q : ℕ) : TopologicalSpace (UpqT P Q) :=
  inferInstanceAs (TopologicalSpace (Formalism.UG.Upq P Q))
instance (P Q : ℕ) : MeasurableSpace (UpqT P Q) := borel (UpqT P Q)

def UpqT.mat {P Q : ℕ} (g : UpqT P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  let g' : Formalism.UG.Upq P Q := g; ((g'.1 : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)

def lieU (P Q : ℕ) : Submodule ℝ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) where
  carrier := {X | Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Formalism.UG.Jpq P Q + Yᴴ * Formalism.UG.Jpq P Q + (Formalism.UG.Jpq P Q * X + Formalism.UG.Jpq P Q * Y)
        = (Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X) + (Yᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * Y) := by
          abel
      _ = 0 := by rw [hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, hX,
      smul_zero]

instance (P Q : ℕ) : MeasurableSpace (lieU P Q) := borel (lieU P Q)

def entries {P Q : ℕ} (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ := fun ij => Z ij.1 ij.2

def IsOmegaLeb {P Q : ℕ} (lam : Measure (lieU P Q)) : Prop :=
  lam.IsAddHaarMeasure ∧
    ((lam.prod lam).map (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) = volume

def ballU (P Q : ℕ) (r : ℝ) : Set (lieU P Q) :=
  {X | ∑ i, ∑ j, ‖(X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r}

def OmegaDensity {P Q : ℕ} (μ : Measure (UpqT P Q)) (c : ENNReal) : Prop :=
  ∃ lam : Measure (lieU P Q), IsOmegaLeb lam ∧
    Tendsto (fun r : ℝ => μ {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c)

structure CDHaar where
  cd : ∀ P Q : ℕ, Measure (UpqT P Q)
  haar : ∀ P Q, (cd P Q).IsHaarMeasure
  prob : ∀ N, IsProbabilityMeasure (cd N 0)
  trick : ∀ P Q, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity (cd P Q) c ∧ OmegaDensity (cd (P + Q) 0) c

end Formalism.BasicNotions
