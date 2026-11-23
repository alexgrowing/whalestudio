import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.CobDim

lemma eval_polySlash (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (x : ℂ) :
    (slP w g p).eval x = ∑ i ∈ Finset.range (w + 1), p.coeff i *
      (((g 0 0 : ℤ) : ℂ) * x + ((g 0 1 : ℤ) : ℂ)) ^ i * (((g 1 0 : ℤ) : ℂ) * x + ((g 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [slP, LinearMap.sum_apply, eval_finset_sum, mul_assoc]

lemma natDeg_lt {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : p.natDegree < w + 1 := by
  by_cases h : p = 0
  · simp [h]
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

def upU (M : ℕ) : SL(2, ℤ) := ⟨!![1, (M : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩

lemma upU_mem (M : ℕ) : upU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [upU]

def loU (M : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ), 1], by simp [Matrix.det_fin_two]⟩

lemma loU_mem (M : ℕ) : loU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [loU]

lemma eval_shift {w M : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) (x : ℂ) : p.eval (x + M) = p.eval x := by
  have h1 := eval_polySlash w (mat (upU M)) p x
  rw [h] at h1
  rw [h1, eval_eq_sum_range' (natDeg_lt hp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [upU, mat, add_comm]

lemma eq_const_of_shift {w M : ℕ} (hM : 0 < M) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) : p = C (p.eval 0) := by
  have hroot : ∀ n : ℕ, (p - C (p.eval 0)).IsRoot ((n : ℂ) * M) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := eval_shift hp h ((n : ℂ) * M)
      simp only [IsRoot, eval_sub, eval_C] at ih ⊢
      push_cast
      rw [add_mul, one_mul, this, ih]
  have hinf : {x | (p - C (p.eval 0)).IsRoot x}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * M) ?_ hroot
    intro a b hab
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    exact_mod_cast mul_right_cancel₀ hM' hab
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

lemma const_eq_zero {w M : ℕ} (hM : 0 < M) (hw : 1 ≤ w) (c : ℂ) (h : slP w (mat (loU M)) (C c) = C c) : c = 0 := by
  have h1 := eval_polySlash w (mat (loU M)) (C c) 1
  rw [h, eval_C, Finset.sum_eq_single 0] at h1
  · simp [loU, mat] at h1
    have hne : ((M : ℂ) + 1) ^ w ≠ 1 := by
      have : (M + 1) ^ w ≠ 1 := by
        have : 1 < (M + 1) ^ w := Nat.one_lt_pow (by omega) (by omega)
        omega
      exact_mod_cast this
    by_contra hc
    exact hne (by
      have := h1.symm
      field_simp at this
      linear_combination this)
  · intro i _ hi
    simp [coeff_C, hi]
  · simp

end GlobalTheory.HeckeFamilyMatrices.CobDim

open GlobalTheory.HeckeFamilyMatrices.CobDim in
theorem GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 0 < M → 1 ≤ w →
    CongruenceSubgroup.Gamma M ≤ Γ → Module.finrank ℂ (B1 Γ w) = w + 1 := by
  intro M Γ w hM hw hΓ
  unfold B1
  rw [LinearMap.finrank_range_of_inj, (degreeLTEquiv ℂ (w + 1)).finrank_eq, Module.finrank_fin_fun]
  intro p q hpq
  rw [← sub_eq_zero, ← map_sub] at hpq
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hfix : ∀ γ : Γ, slP w (mat γ) (r : ℂ[X]) = r := by
    intro γ
    have := congrFun hpq γ
    simpa [sub_eq_zero] using this
  have hc := eq_const_of_shift hM r.2 (hfix ⟨upU M, hΓ (upU_mem M)⟩)
  have h0 : (r : ℂ[X]).eval 0 = 0 := by
    apply const_eq_zero hM hw
    rw [← hc]
    exact hfix ⟨loU M, hΓ (loU_mem M)⟩
  ext1
  rw [hc, h0]
  simp
