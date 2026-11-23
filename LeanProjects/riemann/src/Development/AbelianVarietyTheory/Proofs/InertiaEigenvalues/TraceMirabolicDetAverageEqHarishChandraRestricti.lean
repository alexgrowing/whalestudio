import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

namespace GlobalTheory.ResTr
variable {g : ℕ} [Fact g.Prime]
open Formalism.MainNotions.ArithmeticCylinders

open Classical in
theorem coeff_mirEl {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (h : Gn g r) :
    (mirEl θ a b).coeff h = if mirSet a b h then ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem sum_gl1 (M : Mt g 1) (d : (ZMod g)ˣ) (hM : M.det = d) (F : (ZMod g)ˣ → ℂ) :
    (∑ x : Gn g 1, if M = (x : Mt g 1) then F (Matrix.GeneralLinearGroup.det x) else 0) = F d := by
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hM]; exact d.isUnit)
  have key : ∀ x : Gn g 1, (M = (x : Mt g 1)) ↔ x = hU.unit := by
    intro x
    rw [Units.ext_iff, IsUnit.unit_spec]
    exact eq_comm
  simp_rw [key]
  rw [Finset.sum_ite_eq' Finset.univ hU.unit, if_pos (Finset.mem_univ _)]
  congr 1
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, hM]

theorem tl_last {n : ℕ} (M : Mt g (n + 1)) (i j : Fin n) : tl n M i j = M i.castSucc j.castSucc := by
  unfold tl entN
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem br_last {n : ℕ} (M : Mt g (n + 1)) (i j : Fin 1) : br n 1 M i j = M (Fin.last n) (Fin.last n) := by
  unfold br entN
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [Fin.fin_one_eq_zero]

theorem br_succ {n : ℕ} (M : Mt g (n + 1)) (i j : Fin n) : br 1 n M i j = M i.succ j.succ := by
  unfold br entN
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [add_comm]

theorem tl_zero {n : ℕ} (M : Mt g (n + 1)) (i j : Fin 1) : tl 1 M i j = M 0 0 := by
  unfold tl entN
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [Fin.fin_one_eq_zero]

def ColsId {n : ℕ} (M : Mt g (n + 1)) : Prop :=
  ∀ i j : Fin (n + 1), j ≠ Fin.last n → M i j = if i = j then 1 else 0

def RowsId {n : ℕ} (M : Mt g (n + 1)) : Prop :=
  ∀ i j : Fin (n + 1), i ≠ 0 → M i j = if i = j then 1 else 0

theorem mulVec_of_id {N : ℕ} (M : Mt g N) (x : Fin N → ZMod g) (i : Fin N)
    (h : ∀ j, x j ≠ 0 → M i j = if i = j then 1 else 0) : M.mulVec x i = x i := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hx : x i = 0
    · rw [hx, mul_zero]
    · rw [h i hx, if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hx : x j = 0
    · rw [hx, mul_zero]
    · rw [h j hx, if_neg (Ne.symm hji), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem mirSet_last_iff {n : ℕ} (h : Gn g (n + 1)) :
    mirSet (Pi.single (Fin.last n) 1) false h ↔ ColsId (h : Mt g (n + 1)) := by
  unfold mirSet
  simp only [Bool.false_eq_true, if_false]
  constructor
  · intro H i j hj
    have := congrFun (H (Pi.single j 1) (by simp [single_dotProduct, Pi.single_apply, Ne.symm hj])) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply] using this
  · intro H x hx
    have hx' : x (Fin.last n) = 0 := by simpa [single_dotProduct] using hx
    funext i
    apply mulVec_of_id
    intro j hj
    exact H i j (fun e => hj (e ▸ hx'))

theorem mirSet_zero_iff {n : ℕ} (h : Gn g (n + 1)) :
    mirSet (Pi.single 0 1) true h ↔ RowsId (h : Mt g (n + 1)) := by
  unfold mirSet
  simp only [if_true]
  constructor
  · intro H i j hi
    obtain ⟨c, hc⟩ := H (Pi.single j 1)
    have := congrFun hc i
    rw [Matrix.mulVec_single_one] at this
    simp [Pi.single_apply, hi] at this
    rw [sub_eq_zero] at this
    simpa [Pi.single_apply] using this
  · intro H x
    refine ⟨((h : Mt g (n + 1)).mulVec x - x) 0, ?_⟩
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · have : (h : Mt g (n + 1)).mulVec x i = x i := mulVec_of_id _ _ _ (fun j _ => H i j hi)
      simp [this, hi]

theorem parTl_iff {n : ℕ} (M : Mt g (n + 1)) : (InPar n M ∧ tl n M = 1) ↔ ColsId M := by
  constructor
  · rintro ⟨hP, hT⟩ i j hj
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
    induction i using Fin.lastCases with
    | last =>
      rw [if_neg (Fin.castSucc_ne_last j).symm]
      exact hP _ _ (by simp) (by simp)
    | cast i =>
      have := congrFun (congrFun hT i) j
      rw [tl_last] at this
      rw [this, Matrix.one_apply]
      simp [Fin.castSucc_inj]
  · intro H
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · have hne : j ≠ Fin.last n := fun e => by rw [e] at hj; simp at hj
      rw [H i j hne, if_neg]
      intro e; rw [e] at hi; omega
    · ext i j
      rw [tl_last, H _ _ (Fin.castSucc_ne_last j), Matrix.one_apply]
      simp [Fin.castSucc_inj]

theorem parBr_iff {n : ℕ} (M : Mt g (n + 1)) : (InPar 1 M ∧ br 1 n M = 1) ↔ RowsId M := by
  constructor
  · rintro ⟨hP, hB⟩ i j hi
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hi
    induction j using Fin.cases with
    | zero =>
      rw [if_neg (Fin.succ_ne_zero i)]
      exact hP _ _ (by simp) (by simp)
    | succ j =>
      have := congrFun (congrFun hB i) j
      rw [br_succ] at this
      rw [this, Matrix.one_apply]
      simp [Fin.succ_inj]
  · intro H
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · have hne : i ≠ 0 := fun e => by rw [e] at hi; simp at hi
      rw [H i j hne, if_neg]
      intro e; rw [e] at hi; omega
    · ext i j
      rw [br_succ, H _ _ (Fin.succ_ne_zero i), Matrix.one_apply]
      simp [Fin.succ_inj]

theorem det_colsId {n : ℕ} (M : Mt g (n + 1)) (H : ColsId M) : M.det = M (Fin.last n) (Fin.last n) := by
  have hT : M.BlockTriangular id := by
    intro i j hij
    have hj : j ≠ Fin.last n := fun e => by
      rw [e] at hij; exact absurd hij (not_lt.2 (Fin.le_last i))
    simp only [id] at hij
    rw [H i j hj, if_neg (ne_of_gt hij)]
  rw [Matrix.det_of_upperTriangular hT, Fin.prod_univ_castSucc]
  rw [Finset.prod_eq_one, one_mul]
  intro i _
  rw [H _ _ (Fin.castSucc_ne_last i), if_pos rfl]

theorem det_rowsId {n : ℕ} (M : Mt g (n + 1)) (H : RowsId M) : M.det = M 0 0 := by
  have hT : M.BlockTriangular id := by
    intro i j hij
    have hi : i ≠ 0 := fun e => by
      rw [e] at hij; exact absurd hij (not_lt.2 (Fin.zero_le j))
    simp only [id] at hij
    rw [H i j hi, if_neg (ne_of_gt hij)]
  rw [Matrix.det_of_upperTriangular hT, Fin.prod_univ_succ]
  rw [Finset.prod_eq_one, mul_one]
  intro i _
  rw [H _ _ (Fin.succ_ne_zero i), if_pos rfl]

theorem det_br_last {n : ℕ} (h : Gn g (n + 1)) (H : ColsId (h : Mt g (n + 1))) :
    (br n 1 (h : Mt g (n + 1))).det = ((Matrix.GeneralLinearGroup.det h : (ZMod g)ˣ) : ZMod g) := by
  rw [Matrix.det_unique, br_last, Matrix.GeneralLinearGroup.val_det_apply, det_colsId _ H]

theorem det_tl_zero {n : ℕ} (h : Gn g (n + 1)) (H : RowsId (h : Mt g (n + 1))) :
    (tl 1 (h : Mt g (n + 1))).det = ((Matrix.GeneralLinearGroup.det h : (ZMod g)ˣ) : ZMod g) := by
  rw [Matrix.det_unique, tl_zero, Matrix.GeneralLinearGroup.val_det_apply, det_rowsId _ H]

open Classical in

theorem trace_mir (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (θ : (ZMod g)ˣ →* ℂˣ) :
    tr (mirEl θ (Pi.single (Fin.last n) 1) false) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ∧
      tr (mirEl θ (Pi.single 0 1) true) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 := by
  have hg : (g : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)
  have hc : ∀ a t : ℂ, (g : ℂ) ^ n * (a * (((g : ℂ) ^ n)⁻¹ * t)) = a * t := fun a t => by
    rw [mul_left_comm, mul_inv_cancel_left₀ hg]
  constructor
  · unfold tr res
    simp_rw [coeff_mirEl, mul_one, Finset.mul_sum, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases H : ColsId (h : Mt g (n + 1))
    · obtain ⟨hP, hT⟩ := (parTl_iff _).2 H
      rw [if_pos ((mirSet_last_iff h).2 H)]
      simp only [Units.val_one, hP, hT, true_and, mul_ite, mul_zero]
      rw [sum_gl1 _ _ (det_br_last h H) (fun d => ((θ d : ℂˣ) : ℂ) * ψ h)]
    · rw [if_neg (fun e => H ((mirSet_last_iff h).1 e)), zero_mul]
      refine (Finset.sum_eq_zero (fun x _ => ?_)).symm
      rw [if_neg (fun e => H ((parTl_iff _).1 ⟨e.1, by simpa using e.2.1⟩)), mul_zero]
  · unfold tr res
    simp_rw [coeff_mirEl, one_mul, Finset.mul_sum, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases H : RowsId (h : Mt g (n + 1))
    · obtain ⟨hP, hB⟩ := (parBr_iff _).2 H
      rw [if_pos ((mirSet_zero_iff h).2 H)]
      simp only [Units.val_one, hP, hB, true_and, and_true, mul_ite, mul_zero]
      rw [sum_gl1 _ _ (det_tl_zero h H) (fun d => ((θ d : ℂˣ) : ℂ) * ψ h)]
    · rw [if_neg (fun e => H ((mirSet_zero_iff h).1 e)), zero_mul]
      refine (Finset.sum_eq_zero (fun x _ => ?_)).symm
      rw [if_neg (fun e => H ((parBr_iff _).1 ⟨e.1, by simpa using e.2.2⟩)), mul_zero]
end GlobalTheory.ResTr
