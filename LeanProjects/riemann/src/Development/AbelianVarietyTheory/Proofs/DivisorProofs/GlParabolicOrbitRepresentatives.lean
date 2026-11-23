import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt

open Matrix

namespace GlobalTheory.OrbitsGLParab

variable {k : Type} [Field k]

variable {n m : ℕ}

def cols (X : Matrix (Fin n) (Fin m) k) : Fin m → Fin n → k := fun j r => X r j

theorem exists_coeff (X : Matrix (Fin n) (Fin m) k) (j : Fin m)
    (hj : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j)) :
    ∃ c : Fin m → k, (∀ i, ¬ j < i → c i = 0) ∧ ∀ r, ∑ i, c i * X r i = X r j := by
  obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination k).1 hj
  refine ⟨l, fun i hi => ?_, fun r => ?_⟩
  · by_contra h
    exact hi (hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hx
    have := congrFun hx r
    simpa [Finset.sum_apply, cols] using this

open Classical in

noncomputable def coef (X : Matrix (Fin n) (Fin m) k) : Matrix (Fin m) (Fin m) k :=
  Matrix.of fun i j => if h : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then
    (exists_coeff X j h).choose i else 0

theorem coef_of_not_mem (X : Matrix (Fin n) (Fin m) k) {j : Fin m}
    (hj : cols X j ∉ Submodule.span k (cols X '' Set.Ioi j)) (i : Fin m) : coef X i j = 0 := by
  unfold coef
  simp [hj]

theorem sum_coef (X : Matrix (Fin n) (Fin m) k) {j : Fin m}
    (hj : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j)) (r : Fin n) :
    ∑ i, X r i * coef X i j = X r j := by
  unfold coef
  simp only [of_apply, dif_pos hj]
  rw [← (exists_coeff X j hj).choose_spec.2 r]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

noncomputable def clr (X : Matrix (Fin n) (Fin m) k) : Matrix (Fin m) (Fin m) k := 1 - coef X

open Classical in
theorem mul_clr (X : Matrix (Fin n) (Fin m) k) (r : Fin n) (j : Fin m) :
    (X * clr X) r j = if cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then 0 else X r j := by
  rw [clr, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, mul_apply]
  split_ifs with hj
  · rw [sum_coef X hj, sub_self]
  · simp [coef_of_not_mem X hj]

theorem linInd (X : Matrix (Fin n) (Fin m) k) :
    LinearIndependent k
      (fun j : {j : Fin m // cols X j ∉ Submodule.span k (cols X '' Set.Ioi j)} => cols X j.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  by_contra hne
  set T := s.filter (fun i => g i ≠ 0) with hTdef
  have hT : T.Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  set j := T.min' hT with hjdef
  have hjT : j ∈ T := T.min'_mem hT
  obtain ⟨hjs, hgj⟩ := Finset.mem_filter.1 hjT
  apply j.2
  have key : g j • cols X j.1 = - ∑ i ∈ s.erase j, g i • cols X i.1 := by
    rw [← Finset.add_sum_erase s _ hjs] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have hmem : ∑ i ∈ s.erase j, g i • cols X i.1 ∈ Submodule.span k (cols X '' Set.Ioi j.1) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    by_cases hgi : g i = 0
    · simp [hgi]
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1, ?_, rfl⟩)
      have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hi, hgi⟩
      have hle : j ≤ i := T.min'_le i hiT
      have hne : i ≠ j := Finset.ne_of_mem_erase hi
      exact (lt_of_le_of_ne hle (Ne.symm hne) : j < i)
  have : cols X j.1 = (g j)⁻¹ • (g j • cols X j.1) := by rw [smul_smul, inv_mul_cancel₀ hgj, one_smul]
  rw [this, key]
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)

theorem exists_decomp (X : Matrix (Fin n) (Fin m) k) :
    ∃ (g : GL (Fin n) k) (s : Matrix (Fin n) (Fin m) k), (∀ i j, s i j = 0 ∨ s i j = 1) ∧
      X * clr X = (g : Matrix (Fin n) (Fin n) k) * s := by
  classical
  have hli := linInd X
  let B := Module.Basis.sumExtend hli
  have hB : ∀ j, B (Sum.inl j) = cols X j.1 := by
    intro j
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  let e := B.indexEquiv (Pi.basisFun k (Fin n))
  let b := B.reindex e
  have hb : ∀ j, b (e (Sum.inl j)) = cols X j.1 := by
    intro j
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  let G : Matrix (Fin n) (Fin n) k := Matrix.of fun r l => b l r
  have hG : G = (Pi.basisFun k (Fin n)).toMatrix b := by
    ext r l
    simp [G, Module.Basis.toMatrix_apply]
  have hdet : G.det ≠ 0 := by
    rw [hG]
    have := (Pi.basisFun k (Fin n)).invertibleToMatrix b
    exact (isUnit_det_of_invertible _).ne_zero
  let s : Matrix (Fin n) (Fin m) k := Matrix.of fun r j =>
    if h : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then 0
    else if r = e (Sum.inl ⟨j, h⟩) then 1 else 0
  refine ⟨GeneralLinearGroup.mkOfDetNeZero G hdet, s, fun i j => ?_, ?_⟩
  · simp only [s, of_apply]
    split_ifs <;> simp
  · ext r j
    rw [mul_clr, GeneralLinearGroup.val_mkOfDetNeZero, mul_apply]
    simp only [s, of_apply]
    split_ifs with hj
    · simp
    · rw [Finset.sum_eq_single (e (Sum.inl ⟨j, hj⟩))]
      · have := congrFun (hb ⟨j, hj⟩) r
        simp only [G, of_apply, if_pos rfl, mul_one, dif_neg hj]
        rw [this]
        simp [cols]
      · intro l _ hl
        simp [hl, dif_neg hj]
      · simp

end GlobalTheory.OrbitsGLParab
