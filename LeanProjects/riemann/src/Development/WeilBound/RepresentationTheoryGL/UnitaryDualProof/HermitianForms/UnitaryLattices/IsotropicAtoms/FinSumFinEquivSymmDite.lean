import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Atom

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finSumFinEquiv_symm_dite (n r : ℕ) (x : Fin (n + r)) :
    finSumFinEquiv.symm x = if h : (x : ℕ) < n then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x - n, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem unip_val_apply (n : ℕ) (v : Multiplicative (Fin n → k)) (a b : Fin (n + 1)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (if a = b then 1 else 0) + (if ha : (a : ℕ) < n then (if (b : ℕ) = n then v.toAdd ⟨a, ha⟩ else 0) else 0) := by
  show (1 + colMat k n v.toAdd) a b = _
  rw [Matrix.add_apply, one_apply]
  congr 1
  have hb : (b = Fin.last n) ↔ (b : ℕ) = n := by rw [Fin.ext_iff, Fin.val_last]
  induction a using Fin.lastCases with
  | last => simp [colMat]
  | cast a => simp [colMat, hb]

theorem glEmb_val_apply (n : ℕ) (g : GL (Fin n) k) (a b : Fin (n + 1)) :
    ((glEmb k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      if ha : (a : ℕ) < n then (if hb : (b : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨a, ha⟩ ⟨b, hb⟩ else 0)
      else (if a = b then 1 else 0) := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a b = _
  induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
    simp [glEmbMat, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem eq_unip_glEmb' {n : ℕ} (p : Mir k n) :
    (p : GL (Fin (n + 1)) k) =
      unip k n (Multiplicative.ofAdd fun r => ((p : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.last n)) *
        glEmb k n (mirabolicProjection k n p) := by
  have hh := (mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2
  ext1
  rw [Units.val_mul]
  show _ = (1 + colMat k n _) * glEmbMat k n (blockMat k n (p : GL (Fin (n + 1)) k))
  rw [add_mul, one_mul, colMat_mul_glEmbMat]
  ext a b
  induction a using Fin.lastCases with
  | last =>
    rw [hh]
    induction b using Fin.lastCases <;>
      simp [glEmbMat, colMat, eLast, Fin.castSucc_ne_last, Pi.single_apply]
  | cast a =>
    induction b using Fin.lastCases <;>
      simp [glEmbMat, colMat, blockMat, Fin.castSucc_ne_last]

theorem mem_colFix_iff' (N n : ℕ) (g : GL (Fin N) k) :
    g ∈ colFix k N n ↔ ∀ i j : Fin N, (j : ℕ) < n → (g : Matrix (Fin N) (Fin N) k) i j = if i = j then 1 else 0 := by
  constructor
  · intro hg i j hj
    have := congrFun (hg j hj) i
    simpa [mulVec, dotProduct, Pi.single_apply, eq_comm] using this
  · intro hg j hj
    funext i
    simp [mulVec, dotProduct, Pi.single_apply, hg i j hj]

theorem blkAt_val_apply (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    ((blkAt k n N h g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      if hi : (i : ℕ) < n then (if hj : (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else (if i = j then 1 else 0) := by
  show (reindexAlgEquiv k k (finCongr (Nat.add_sub_cancel' h))
    (reindexAlgEquiv k k finSumFinEquiv (fromBlocks (g : Matrix (Fin n) (Fin n) k) 0 0 1))) i j = _
  rw [coe_reindexAlgEquiv, coe_reindexAlgEquiv, reindex_apply, reindex_apply, submatrix_apply, submatrix_apply]
  simp only [finCongr_symm, finCongr_apply, finSumFinEquiv_symm_dite, Fin.val_cast]
  by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;>
    simp [hi, hj, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, one_apply,
      Fin.ext_iff]
  all_goals (try split_ifs) <;> first | rfl | omega

theorem colEl_add (m N : ℕ) (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  simp only [colEl, ofAdd_add, map_mul]

theorem colEl_zero (m N : ℕ) (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  simp [colEl]

theorem colEl_val_apply (m N : ℕ) (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i j : Fin N) :
    ((colEl k m N h x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (if i = j then 1 else 0) + (if hi : (i : ℕ) < m + 1 then (if (j : ℕ) = m + 1 then x ⟨i, hi⟩ else 0) else 0) := by
  rw [colEl, blkAt_val_apply]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;> simp only [hi, hj, dite_true, dite_false]
  · rw [unip_val_apply]
    simp only [Fin.ext_iff, toAdd_ofAdd]
  · simp [Fin.ext_iff, show ¬ (i : ℕ) = j by omega, show ¬ (j : ℕ) = m + 1 by omega]
  · simp [Fin.ext_iff]; omega
  · simp
    intro h1 h2
    omega

theorem continuous_colEl (m N : ℕ) (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  have hc : Continuous fun x => ((colEl k m N h x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    refine continuous_matrix fun i j => ?_
    simp only [colEl_val_apply]
    by_cases hi : (i : ℕ) < m + 1 <;> by_cases hj : (j : ℕ) = m + 1 <;> simp only [hi, hj, dite_true, dite_false,
      if_true, if_false] <;> fun_prop
  have hinv : ∀ x, ((colEl k m N h x)⁻¹ : GL (Fin N) k) = colEl k m N h (-x) := fun x => by
    rw [eq_comm, eq_inv_iff_mul_eq_one, ← colEl_add, neg_add_cancel, colEl_zero]
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  exact (hc.comp continuous_neg).congr fun x => by simp only [Function.comp, hinv]

theorem blkAt_glEmb (m N : ℕ) (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) :
    blkAt k (m + 2) N h (glEmb k (m + 1) g) = blkAt k (m + 1) N (by omega) g := by
  ext i j
  rw [blkAt_val_apply, blkAt_val_apply]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>
    simp only [hi, hj, dite_true, dite_false, glEmb_val_apply]
  all_goals (try split_ifs) <;> simp_all [Fin.ext_iff] <;> omega

theorem det_glEmb (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (glEmb k n g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  show (glEmbMat k n (g : Matrix (Fin n) (Fin n) k)).det = _
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  have e : (glEmbMat k n (g : Matrix (Fin n) (Fin n) k)).submatrix (Fin.last n).succAbove (Fin.last n).succAbove =
      (g : Matrix (Fin n) (Fin n) k) := by
    ext a b
    simp [glEmbMat]
  simp only [e]
  simp [glEmbMat, ← two_mul]

theorem det_unip (n : ℕ) (x : Multiplicative (Fin n → k)) : Matrix.GeneralLinearGroup.det (unip k n x) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    rw [unip_val_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · intro a b hab
    rw [unip_val_apply]
    have hab' : (b : ℕ) < a := hab
    split_ifs <;> first | (exfalso; omega) | simp_all [Fin.ext_iff]

theorem blkAt_mul_colEl (m N : ℕ) (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) :
    blkAt k (m + 1) N (by omega) g * colEl k m N h x =
      colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec x) * blkAt k (m + 1) N (by omega) g := by
  rw [← blkAt_glEmb m N h g, colEl, colEl, ← map_mul, ← map_mul, glEmb_mul_unip']
  rfl

theorem unip_mem_Mir (m : ℕ) (x : Fin (m + 1) → k) : unip k (m + 1) (Multiplicative.ofAdd x) ∈ Mir k (m + 1) := by
  exact MirU_le_Mir k (m + 1) ⟨_, rfl⟩

theorem glEmb_mem_Mir' (m : ℕ) (g : GL (Fin (m + 1)) k) : glEmb k (m + 1) g ∈ Mir k (m + 1) := glEmb_mem_Mir k (m + 1) g

theorem mir_decomp (m N : ℕ) (h : m + 2 ≤ N) (p : GL (Fin (m + 2)) k) (hp : p ∈ Mir k (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (g : GL (Fin (m + 1)) k),
      blkAt k (m + 2) N h p = colEl k m N h x * blkAt k (m + 1) N (by omega) g ∧
      Matrix.GeneralLinearGroup.det p = Matrix.GeneralLinearGroup.det g := by
  have e : p = _ := eq_unip_glEmb' (⟨p, hp⟩ : Mir k (m + 1))
  refine ⟨fun r => (p : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (Fin.castSucc r) (Fin.last (m + 1)),
    mirabolicProjection k (m + 1) ⟨p, hp⟩, ?_, ?_⟩
  · conv_lhs => rw [e]
    rw [map_mul, ← blkAt_glEmb m N h]
    rfl
  · calc Matrix.GeneralLinearGroup.det p = Matrix.GeneralLinearGroup.det (unip k (m + 1) _ * glEmb k (m + 1) _) :=
          congrArg _ e
      _ = _ := by rw [map_mul, det_unip, one_mul, det_glEmb]

theorem derUnip_decomp (ψ : AddChar k Circle) (m N : ℕ) (h : m + 2 ≤ N) (u : GL (Fin N) k)
    (hu : u ∈ derUnip k N (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (u' : GL (Fin N) k) (hu' : u' ∈ derUnip k N (m + 2)),
      u = colEl k m N h x * u' ∧
      ((derChar k ψ N (m + 1) ⟨u, hu⟩ : ℂˣ) : ℂ) = ((lvlChar k ψ N (m + 2) ⟨u', hu'⟩ : ℂˣ) : ℂ) := by
  have hu1 := (mem_unipB k).1 (Subgroup.mem_inf.1 hu).1
  have hcf := (mem_colFix_iff' N (m + 1) u).1 (Subgroup.mem_inf.1 hu).2
  have hlow : ∀ i j : Fin N, (j : ℕ) < i → (u : Matrix (Fin N) (Fin N) k) i j = 0 := fun i j hij => hu1.1 i j hij
  have hdiag := hu1.2
  set r : Fin N := ⟨m + 1, by omega⟩ with hr
  set x : Fin (m + 1) → k := fun i => (u : Matrix (Fin N) (Fin N) k) ⟨i, by omega⟩ r with hx
  set u' : GL (Fin N) k := colEl k m N h (-x) * u with hu'def
  have hent : ∀ i j, (u' : Matrix (Fin N) (Fin N) k) i j = (u : Matrix (Fin N) (Fin N) k) i j -
      (if hi : (i : ℕ) < m + 1 then x ⟨i, hi⟩ * (u : Matrix (Fin N) (Fin N) k) r j else 0) := by
    intro i j
    rw [hu'def, Units.val_mul, mul_apply]
    simp only [colEl_val_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    by_cases hi : (i : ℕ) < m + 1
    · simp only [hi, dite_true, ite_mul, zero_mul]
      rw [Finset.sum_eq_single r (fun b _ hb => if_neg (fun e => hb (Fin.ext e))) (by simp)]
      simp [hr, sub_eq_add_neg]
    · simp [hi]
  have hu' : u' ∈ derUnip k N (m + 2) := by
    refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩, (mem_colFix_iff' N (m + 2) u').2 fun i j hj => ?_⟩
    · have hij' : (j : ℕ) < i := hij
      rw [hent, hlow i j hij']
      split_ifs with hi
      · rw [hlow r j (by simp [hr]; omega)]; simp
      · simp
    · rw [hent, hdiag]
      split_ifs with hi
      · rw [hlow r i (by simp [hr]; omega)]; simp
      · simp
    · rw [hent]
      by_cases hj' : (j : ℕ) < m + 1
      · rw [hcf i j hj', hcf r j hj']
        simp [hr, Fin.ext_iff]
        intro _ e
        omega
      · have hjr : j = r := Fin.ext (by simp [hr]; omega)
        rw [hjr, hdiag r]
        by_cases hi : (i : ℕ) < m + 1
        · simp [hi, hx, hr, Fin.ext_iff, show (i : ℕ) ≠ m + 1 by omega]
        · by_cases hir : i = r
          · rw [hir, hdiag r]; simp [hr]
          · have : (r : ℕ) < i := by
              have := Fin.val_ne_of_ne hir
              simp [hr] at this ⊢; omega
            rw [hlow i r this]; simp [hi, hir]
  refine ⟨x, u', hu', ?_, ?_⟩
  · rw [hu'def, ← mul_assoc, ← colEl_add, add_neg_cancel, colEl_zero, one_mul]
  · have hs : (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), (u : Matrix (Fin N) (Fin N) k) p.1 p.2) =
        ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ), (u' : Matrix (Fin N) (Fin N) k) p.1 p.2 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := (Finset.mem_filter.1 hp).2
      rw [hent, dif_neg (by omega), sub_zero]
    exact congrArg (fun t => ((Circle.toUnits (ψ t) : ℂˣ) : ℂ)) hs

end PositivityTheory.RgUd.Form.U.Atom
