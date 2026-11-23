import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open Formalism.ConjugateSelfDual
open scoped Matrix

namespace GlobalTheory.SmallMat

variable {l : ℕ} [Fact l.Prime]

def Sm (ε : ℝ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) : Prop := ∀ i j, ‖M i j‖ ≤ ε

theorem Sm.mono {ε δ : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (h : Sm ε M) (hεδ : ε ≤ δ) : Sm δ M :=
  fun i j => (h i j).trans hεδ

theorem Sm.add {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M + N) := fun i j => by
  simp only [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

theorem Sm.neg {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) : Sm ε (-M) := fun i j => by
  simpa using hM i j

theorem Sm.sub {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M - N) := by
  rw [sub_eq_add_neg]; exact hM.add hN.neg

theorem sm_zero {ε : ℝ} (hε : 0 ≤ ε) : Sm (l := l) ε 0 := fun i j => by simpa using hε

theorem Sm.mul {ε δ : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm δ N) (hε : 0 ≤ ε) :
    Sm (ε * δ) (M * N) := fun i j => by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact mul_le_mul (hM _ _) (hN _ _) (norm_nonneg _) hε

theorem Sm.smul {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (a : Qbar l) : Sm (‖a‖ * ε) (a • M) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]; exact mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)

theorem Sm.smul_le {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) {a : Qbar l} (ha : ‖a‖ ≤ 1) :
    Sm ε (a • M) :=
  (hM.smul a).mono (by simpa using mul_le_mul_of_nonneg_right ha hε)

theorem sm_scalar {ε : ℝ} {a : Qbar l} (ha : ‖a‖ ≤ ε) (hε : 0 ≤ ε) : Sm ε (a • (1 : Matrix (Fin 2) (Fin 2) (Qbar l))) :=
  fun i j => by
    by_cases h : i = j
    · subst h; simpa using ha
    · simpa [Matrix.one_apply_ne h] using hε

theorem Sm.sum {ι : Type*} (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (M : ι → Matrix (Fin 2) (Fin 2) (Qbar l))
    (h : ∀ i ∈ s, Sm ε (M i)) : Sm ε (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun i hi => h i hi a b

theorem norm_natCast_le_one (b : ℕ) : ‖(b : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ b

theorem Sm.det {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) : ‖M.det‖ ≤ ε ^ 2 := by
  rw [Matrix.det_fin_two, sq, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> simp only [norm_neg, norm_mul] <;>
    exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hε

end GlobalTheory.SmallMat

end
