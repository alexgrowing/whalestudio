import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly.DiscLin

theorem rootProd_eq_det {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ a : Fin N, ∏ b : Fin N, if a < b then v a - v b else 1) =
      (Matrix.vandermonde (fun i => -v i)).det := by
  rw [Matrix.det_vandermonde]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr (by ext b; simp) fun b _ => by ring

theorem rootProd_swap {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) (a b : Fin N) (hab : a ≠ b) :
    (∏ c : Fin N, ∏ d : Fin N, if c < d then v (Equiv.swap a b c) - v (Equiv.swap a b d) else 1) =
      -(∏ c : Fin N, ∏ d : Fin N, if c < d then v c - v d else 1) := by
  rw [rootProd_eq_det (fun c => v (Equiv.swap a b c)), rootProd_eq_det v]
  have h : Matrix.vandermonde (fun i => -v (Equiv.swap a b i)) =
      (Matrix.vandermonde (fun i => -v i)).submatrix (Equiv.swap a b) id := by
    ext i k; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute, Equiv.Perm.sign_swap hab]
  simp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem rename_swapAt_delPol (τ : ι) (a b : Fin N) (hab : a ≠ b) :
    rename (swapAt τ a b) (delPol ι N) = -delPol ι N := by
  unfold delPol
  rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), ← neg_mul]
  congr 1
  · rw [← rootProd_swap (fun c => (X (τ, c) : Pol ι N)) a b hab]
    simp only [map_prod]
    refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun d _ => ?_
    split_ifs <;> simp [swapAt]
  · refine Finset.prod_congr rfl fun t ht => ?_
    have ht' : t ≠ τ := Finset.ne_of_mem_erase ht
    simp only [map_prod]
    refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun d _ => ?_
    split_ifs <;> simp [swapAt, ht']

theorem rename_swapAt_sum (τ t : ι) (a b : Fin N) (p : Fin N → Prop) [DecidablePred p]
    (hp : p a ↔ p b) :
    rename (swapAt τ a b) (∑ i ∈ Finset.univ.filter p, (X (t, i) : Pol ι N) ^ 1) =
      ∑ i ∈ Finset.univ.filter p, (X (t, i) : Pol ι N) ^ 1 := by
  simp only [map_sum, pow_one, rename_X, swapAt]
  by_cases ht : t = τ
  · simp only [ht, if_true]
    refine Finset.sum_equiv (Equiv.swap a b) (fun i => ?_) (fun i _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : i = a
    · subst h1; simpa using hp
    · by_cases h2 : i = b
      · subst h2; simpa using hp.symm
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · simp [ht]

theorem rename_swapAt_invForm (j : ℕ) (al be : ι → ℝ) (τ : ι) (a b : Fin N)
    (h1 : (b : ℕ) = a + 1) (h2 : (b : ℕ) ≠ j) :
    rename (swapAt τ a b) (invForm (N := N) j al be) = invForm j al be := by
  unfold invForm pLow pHigh
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_add, map_mul, map_mul, rename_C, rename_C,
    rename_swapAt_sum τ t a b (fun i : Fin N => (i : ℕ) < j) (by omega),
    rename_swapAt_sum τ t a b (fun i : Fin N => j ≤ (i : ℕ)) (by omega)]

theorem invForm_isHomogeneous (j : ℕ) (al be : ι → ℝ) :
    (invForm (N := N) j al be).IsHomogeneous 1 := by
  unfold invForm pLow pHigh
  refine IsHomogeneous.sum _ _ _ fun t _ => IsHomogeneous.add ?_ ?_
  all_goals
    refine IsHomogeneous.C_mul (IsHomogeneous.sum _ _ _ fun i _ => ?_) _
    rw [pow_one]; exact isHomogeneous_X _ _

theorem sum_pairs (N : ℕ) :
    (∑ a : Fin N, ∑ b : Fin N, if a < b then 1 else 0 : ℕ) = N * (N - 1) / 2 := by
  rw [← PermutationPointDegree.sum_delta N]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_filter, ← Fin.card_Ioi]
  congr 1; ext b; simp

theorem delPol_isHomogeneous : (delPol ι N).IsHomogeneous (dimFl ι N) := by
  have h : dimFl ι N = ∑ _τ : ι, ∑ a : Fin N, ∑ b : Fin N, if a < b then 1 else 0 := by
    rw [sum_pairs]; simp [dimFl]
  rw [h]
  unfold delPol
  refine IsHomogeneous.prod _ _ _ fun t _ => IsHomogeneous.prod _ _ _ fun a _ =>
    IsHomogeneous.prod _ _ _ fun b _ => ?_
  split_ifs
  · exact (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  · exact isHomogeneous_one _ _

theorem delPol_mul_invForm (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (al be : ι → ℝ) :
    AntiL j (delPol ι N * invForm j al be) ∧
      (delPol ι N * invForm (N := N) j al be).IsHomogeneous (dimFl ι N + 1) := by
  refine ⟨fun τ a b h1 h2 => ?_, delPol_isHomogeneous.mul (invForm_isHomogeneous j al be)⟩
  have hab : a ≠ b := fun h => by rw [h] at h1; omega
  rw [map_mul, rename_swapAt_delPol τ a b hab, rename_swapAt_invForm j al be τ a b h1 h2, neg_mul]

end GlobalTheory.FlagPoly.DiscLin
