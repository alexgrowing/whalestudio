import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwTangent

variable {n : ℕ}

open scoped Matrix.Norms.Frobenius

theorem coe_smul_eq (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : (t : ℂ) • X = t • X := by
  ext i j; simp

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hs' := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at hs'
  have hc : IsClosed (A : Set (Matrix (Fin n) (Fin n) ℂ)) := A.closed_of_finiteDimensional
  exact hc.mem_of_tendsto hs'.tendsto_sum_nat (Filter.Eventually.of_forall fun m =>
    A.sum_mem fun k _ => A.smul_mem _ (hp k))

theorem mem_of_exp_sub_one_mem (T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) - 1 ∈ T) : X ∈ T := by
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  have hc : IsClosed (T : Set (Matrix (Fin n) (Fin n) ℂ)) := T.closed_of_finiteDimensional
  refine hc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  simp only [zero_add, zero_smul, NormedSpace.exp_zero]
  exact T.smul_mem _ (h t)

theorem exists_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (t : ℝ) :
    ∃ g : Formalism.REAL.UJ ε, uMat g = NormedSpace.exp (t • X) :=
  ⟨GlobalTheory.GaugeConst.expJ ε ⟨t • X, (GlobalTheory.GaugeConst.lieJ ε).smul_mem t hX⟩, rfl⟩

theorem lie_algebra_of_isCut : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  rintro n ε S d E ⟨A, hA, -, hE, rfl⟩
  simp only [coe_smul_eq]
  have h1 : ∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ,
      ∃ g ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A}, uMat g = NormedSpace.exp (t • X) := by
    intro X hX t
    obtain ⟨hXA, hXG⟩ := (hE X).2 hX
    obtain ⟨g, hg⟩ := exists_exp hXG t
    refine ⟨g, ?_, hg⟩
    change uMat g - 1 ∈ A
    rw [hg]
    exact exp_sub_one_mem A hA (A.smul_mem t hXA)
  refine ⟨h1, fun T hT i => mem_of_exp_sub_one_mem T _ fun t => ?_, fun X hX h => (hE X).1 ⟨?_, hX⟩⟩
  · obtain ⟨g, hg, hg'⟩ := h1 (E i) (Submodule.subset_span ⟨i, rfl⟩) t
    rw [← hg']
    exact hT g hg
  · refine mem_of_exp_sub_one_mem A _ fun t => ?_
    obtain ⟨g, hg⟩ := exists_exp hX t
    rw [← hg]
    exact h t g hg

end GlobalTheory.IwTangent
