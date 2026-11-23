import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep

noncomputable section

namespace PI.UnitaryGroupMassFormula.CommMult

open MeasureTheory Matrix

section Integral

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

def mInt (μ : Measure H) {m n : Type} (F : H → Matrix m n ℂ) : Matrix m n ℂ :=
  Matrix.of fun i j => ∫ h, F h i j ∂μ

lemma integrable_entry (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {m n : Type}
    {F : H → Matrix m n ℂ} (hF : Continuous F) (i : m) (j : n) :
    Integrable (fun h => F h i j) μ :=
  (hF.matrix_elem i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma mul_mInt (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {l m n : Type} [Fintype m]
    (A : Matrix l m ℂ) {F : H → Matrix m n ℂ} (hF : Continuous F) :
    A * mInt μ F = mInt μ (fun h => A * F h) := by
  ext i j
  simp only [mInt, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ (fun k _ => (integrable_entry μ hF k j).const_mul (A i k))]
  simp only [integral_const_mul]

lemma mInt_mul (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {l m n : Type} [Fintype m]
    {F : H → Matrix l m ℂ} (hF : Continuous F) (B : Matrix m n ℂ) :
    mInt μ F * B = mInt μ (fun h => F h * B) := by
  ext i j
  simp only [mInt, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ (fun k _ => (integrable_entry μ hF i k).mul_const (B k j))]
  simp only [integral_mul_const]

lemma mInt_const (μ : Measure H) {m n : Type} (C : Matrix m n ℂ) :
    mInt μ (fun _ => C) = μ.real Set.univ • C := by
  ext i j
  simp [mInt, integral_const]

lemma mInt_left (μ : Measure H) [μ.IsMulLeftInvariant] {m n : Type} (F : H → Matrix m n ℂ)
    (g : H) : mInt μ (fun h => F (g * h)) = mInt μ F := by
  ext i j
  simp only [mInt, Matrix.of_apply]
  exact integral_mul_left_eq_self (fun h => F h i j) g

end Integral

theorem avStep : AvStep := by
  intro H _ _ _ _ _ N M π σ hπ hσ T X hT hXT
  let _ : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  set μ : Measure H := Measure.haar with hμ
  set F : H → Matrix (Fin M) (Fin N) ℂ := fun h =>
    ((σ h : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * X *
      ((π h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hFdef
  have hπi : Continuous (fun h : H => ((π h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) :=
    (show Continuous (fun g : H => ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) from hπ).comp
      continuous_inv
  have hF : Continuous F :=
    ((show Continuous (fun g : H => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) from
      hσ).matrix_mul continuous_const).matrix_mul hπi
  set S₀ := mInt μ F with hS₀
  have hequi : ∀ g, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * S₀ =
      S₀ * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    intro g
    have hFg : Continuous (fun h => F (g * h)) := hF.comp (continuous_const.mul continuous_id)
    have hpt : (fun h => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * F h) =
        (fun h => F (g * h) * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by
      funext h
      simp only [hFdef, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ), ← Units.val_mul,
        ← map_mul, ← Units.val_mul (π (g * h)⁻¹), ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    rw [hS₀, mul_mInt μ _ hF, hpt, ← mInt_mul μ hFg, mInt_left μ F g]
  have hST : S₀ * T = μ.real Set.univ • (1 : Matrix (Fin M) (Fin M) ℂ) := by
    have hpt : (fun h => F h * T) = (fun _ => (1 : Matrix (Fin M) (Fin M) ℂ)) := by
      funext h
      simp only [hFdef]
      rw [Matrix.mul_assoc, hT h⁻¹, ← Matrix.mul_assoc, Matrix.mul_assoc _ X T,
        hXT, Matrix.mul_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [hS₀, mInt_mul μ hF, hpt, mInt_const]
  have hc : 0 < μ.real Set.univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
      (measure_ne_top μ _)
  refine ⟨(μ.real Set.univ)⁻¹ • S₀, fun g => ?_, ?_⟩
  · rw [Matrix.mul_smul, hequi g, Matrix.smul_mul]
  · rw [Matrix.smul_mul, hST, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

end PI.UnitaryGroupMassFormula.CommMult
