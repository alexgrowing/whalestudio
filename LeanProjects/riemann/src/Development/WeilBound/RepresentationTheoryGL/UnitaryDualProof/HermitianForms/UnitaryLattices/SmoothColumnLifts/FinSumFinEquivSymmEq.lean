import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.AvgData

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir PositivityTheory.RgUd.Form

namespace PositivityTheory.RgUd.Form.U.Lift2.TrM

section Alg

variable {k : Type} [Field k]

theorem finSumFinEquiv_symm_eq {a b : ℕ} (x : Fin (a + b)) :
    finSumFinEquiv.symm x = if h : (x : ℕ) < a then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x - a, by omega⟩ := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · simp [finSumFinEquiv_symm_apply_castAdd, i.2]
  · simp [finSumFinEquiv_symm_apply_natAdd]

theorem blkAt_val (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    ((blkAt k n N h g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      if hi : (i : ℕ) < n then (if hj : (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else if i = j then 1 else 0 := by
  have e1 : ((blkAt k n N h g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      reindex (finCongr (Nat.add_sub_cancel' h)) (finCongr (Nat.add_sub_cancel' h))
        (reindex finSumFinEquiv finSumFinEquiv (fromBlocks (g : Matrix (Fin n) (Fin n) k) 0 0 1)) := rfl
  rw [e1, reindex_apply, reindex_apply, submatrix_apply, submatrix_apply, finSumFinEquiv_symm_eq,
    finSumFinEquiv_symm_eq]
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast]
  by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n
  · simp [hi, hj]
  · simp [hi, hj]
  · have hne : i ≠ j := fun e => hi (e ▸ hj)
    simp [hi, hj, hne]
  · simp only [hi, hj, dite_false, fromBlocks_apply₂₂, one_apply, Fin.ext_iff]
    by_cases e : (i : ℕ) = j
    · simp [e]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem glEmbMat_apply' (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (i j : Fin (n + 1)) :
    glEmbMat k n A i j = if hi : (i : ℕ) < n then (if hj : (j : ℕ) < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else if i = j then 1 else 0 := by
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast j => simp [glEmbMat, Fin.ext_iff]; omega
  | cast i => induction j using Fin.lastCases with
    | last => simp [glEmbMat, Fin.ext_iff]
    | cast j => simp [glEmbMat]

theorem blkAt_glEmb (n N : ℕ) (h : n ≤ N) (h' : n + 1 ≤ N) (g : GL (Fin n) k) :
    blkAt k n N h g = blkAt k (n + 1) N h' (glEmb k n g) := by
  ext i j
  rw [blkAt_val, blkAt_val]
  have e : ((glEmb k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (g : Matrix (Fin n) (Fin n) k) := rfl
  simp only [e, glEmbMat_apply']
  by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;> by_cases hi' : (i : ℕ) < n + 1 <;>
    by_cases hj' : (j : ℕ) < n + 1 <;> simp [hi, hj, hi', hj', Fin.ext_iff] <;> omega

theorem blkAt_glEmb' (m N : ℕ) (h : m + 2 ≤ N) (h' : m + 1 ≤ N) (g : GL (Fin (m + 1)) k) :
    blkAt k (m + 1) N h' g = blkAt k (m + 2) N h (glEmb k (m + 1) g) :=
  blkAt_glEmb (m + 1) N h' h g

theorem colEl_zero (m N : ℕ) (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  simp [colEl]

theorem colEl_add (m N : ℕ) (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  simp only [colEl, ofAdd_add, map_mul]

theorem blkAt_mul_colEl (m N : ℕ) (h : m + 2 ≤ N) (h' : m + 1 ≤ N) (g : GL (Fin (m + 1)) k)
    (x : Fin (m + 1) → k) :
    blkAt k (m + 1) N h' g * colEl k m N h x =
      colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) * blkAt k (m + 1) N h' g := by
  rw [blkAt_glEmb' m N h h', colEl, colEl, ← map_mul, ← map_mul, glEmb_mul_unip']
  rfl

theorem lastCases_mk {n : ℕ} (x : Fin n → k) (r : ℕ) (hr : r < n + 1) :
    (Fin.lastCases (0 : k) x (⟨r, hr⟩ : Fin (n + 1)) : k) = if h : r < n then x ⟨r, h⟩ else 0 := by
  by_cases h : r < n
  · have e : (⟨r, hr⟩ : Fin (n + 1)) = Fin.castSucc ⟨r, h⟩ := rfl
    rw [e, Fin.lastCases_castSucc, dif_pos h]
  · have e : (⟨r, hr⟩ : Fin (n + 1)) = Fin.last n := by ext; simp; omega
    rw [e, Fin.lastCases_last, dif_neg h]

theorem colEl_val (m N : ℕ) (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (r c : Fin N) :
    ((colEl k m N h x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) r c =
      (if r = c then 1 else 0) + (if hr : (r : ℕ) < m + 1 then (if (c : ℕ) = m + 1 then x ⟨r, hr⟩ else 0) else 0) := by
  rw [colEl, blkAt_val]
  have e : ((unip k (m + 1) (Multiplicative.ofAdd x) : GL (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k) =
      1 + colMat k (m + 1) x := rfl
  rw [e]
  by_cases hr : (r : ℕ) < m + 2 <;> by_cases hc : (c : ℕ) < m + 2
  · simp only [hr, hc, dite_true, Matrix.add_apply]
    have e3 : colMat k (m + 1) x ⟨r, hr⟩ ⟨c, hc⟩ =
        if (c : ℕ) = m + 1 then (if h : (r : ℕ) < m + 1 then x ⟨r, h⟩ else 0) else 0 := by
      simp only [colMat, Fin.ext_iff, Fin.val_last, lastCases_mk]
    have e4 : (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) k) ⟨r, hr⟩ ⟨c, hc⟩ = if r = c then 1 else 0 := by
      simp only [one_apply, Fin.ext_iff]
    rw [e3, e4]
    by_cases hr' : (r : ℕ) < m + 1 <;> by_cases hc' : (c : ℕ) = m + 1 <;> simp [hr', hc']
  · have hne : r ≠ c := fun e => hc (e ▸ hr)
    have hc' : (c : ℕ) ≠ m + 1 := by omega
    simp [hr, hc, hne, hc']
  · have hne : r ≠ c := fun e => hr (e ▸ hc)
    have hr' : ¬ (r : ℕ) < m + 1 := by omega
    simp [hr, hc, hne, hr']
  · have hr' : ¬ (r : ℕ) < m + 1 := by omega
    simp [hr, hc, hr']

theorem det_glEmbMat' (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  have hs : (glEmbMat k n A).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    simp [glEmbMat]
  simp [glEmbMat, hs]

theorem det_unip' (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have e : ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 + colMat k n v.toAdd := rfl
  have htri : (1 + colMat k n v.toAdd).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    have hj : j ≠ Fin.last n := by
      rintro rfl
      exact absurd hij' (not_lt.2 (Fin.le_last i))
    simp [colMat, hj, one_apply, hij'.ne']
  rw [e, Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  induction i using Fin.lastCases with
  | last => simp [colMat]
  | cast i => simp [colMat, Fin.castSucc_ne_last]

theorem det_unip_GL (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
  ext
  simp [det_unip']

theorem det_glEmb_GL (n : ℕ) (g : GL (Fin n) k) : GeneralLinearGroup.det (glEmb k n g) = GeneralLinearGroup.det g := by
  ext
  exact det_glEmbMat' n (g : Matrix (Fin n) (Fin n) k)

theorem mir_decomp (n : ℕ) (p : GL (Fin (n + 1)) k) (hp : p ∈ Mir k n) :
    ∃ (x : Fin n → k) (g : GL (Fin n) k), p = unip k n (Multiplicative.ofAdd x) * glEmb k n g := by
  have hl := (mem_Mir_iff k p).1 hp
  refine ⟨fun i => (p : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n),
    mirabolicProjection k n ⟨p, hp⟩, ?_⟩
  ext i j
  rw [Units.val_mul]
  have e1 : ((unip k n (Multiplicative.ofAdd (fun i => (p : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i)
      (Fin.last n))) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + colMat k n (fun i => (p : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)) := rfl
  have e2 : ((glEmb k n (mirabolicProjection k n ⟨p, hp⟩) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (blockMat k n (p : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) := rfl
  rw [e1, e2, add_mul, one_mul, colMat_mul_glEmbMat, Matrix.add_apply]
  induction i using Fin.lastCases with
  | last =>
    have := congrFun hl j
    induction j using Fin.lastCases with
    | last => simp [glEmbMat, colMat] at this ⊢; simpa [eLast] using this
    | cast j => simp [glEmbMat, colMat, Fin.castSucc_ne_last] at this ⊢; simpa [eLast, Fin.castSucc_ne_last] using this
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [glEmbMat, colMat]
    | cast j => simp [glEmbMat, colMat, blockMat, Fin.castSucc_ne_last]

theorem det_unip_mul_glEmb (n : ℕ) (x : Fin n → k) (g : GL (Fin n) k) :
    GeneralLinearGroup.det (unip k n (Multiplicative.ofAdd x) * glEmb k n g) = GeneralLinearGroup.det g := by
  rw [map_mul, det_unip_GL, det_glEmb_GL, one_mul]

end Alg

section Conj

variable {k : Type} [Field k]

theorem conj_mat (N a : ℕ) (B C U : Matrix (Fin N) (Fin N) k) (hBC : B * C = 1)
    (hB : ∀ r l : Fin N, (a ≤ (r : ℕ) ∨ a ≤ (l : ℕ)) → B r l = if r = l then 1 else 0)
    (hC : ∀ r l : Fin N, (a ≤ (r : ℕ) ∨ a ≤ (l : ℕ)) → C r l = if r = l then 1 else 0)
    (h1 : ∀ i j : Fin N, j < i → U i j = 0) (h2 : ∀ i, U i i = 1)
    (h3 : ∀ i j : Fin N, (j : ℕ) < a + 1 → U i j = if i = j then 1 else 0) :
    (∀ i j : Fin N, j < i → (B * U * C) i j = 0) ∧ (∀ i, (B * U * C) i i = 1) ∧
      (∀ i j : Fin N, (j : ℕ) < a + 1 → (B * U * C) i j = if i = j then 1 else 0) ∧
      (∀ i j : Fin N, a ≤ (i : ℕ) → (B * U * C) i j = U i j) := by
  have hXcol : ∀ r c : Fin N, (c : ℕ) < a + 1 → (U - 1) r c = 0 := by
    intro r c hc
    rw [Matrix.sub_apply, h3 r c hc, one_apply, sub_self]
  have hXlow : ∀ r c : Fin N, c ≤ r → (U - 1) r c = 0 := by
    intro r c hcr
    rcases hcr.lt_or_eq with hlt | heq
    · rw [Matrix.sub_apply, h1 r c hlt, one_apply_ne hlt.ne', sub_self]
    · subst heq
      rw [Matrix.sub_apply, h2, one_apply_eq, sub_self]
  have hXC : (U - 1) * C = U - 1 := by
    ext r c
    rw [mul_apply, Finset.sum_eq_single c]
    · by_cases hc : (c : ℕ) < a + 1
      · rw [hXcol r c hc, zero_mul]
      · rw [hC c c (Or.inl (by omega)), if_pos rfl, mul_one]
    · intro j _ hjc
      by_cases hj : (j : ℕ) < a + 1
      · rw [hXcol r j hj, zero_mul]
      · rw [hC j c (Or.inl (by omega)), if_neg hjc, mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ c) hc
  have hE : B * U * C = 1 + B * (U - 1) := by
    calc B * U * C = B * (1 + (U - 1)) * C := by rw [add_sub_cancel]
      _ = 1 + B * (U - 1) := by rw [mul_add, mul_one, add_mul, hBC, mul_assoc, hXC]
  have hBXcol : ∀ r c : Fin N, (c : ℕ) < a + 1 → (B * (U - 1)) r c = 0 := by
    intro r c hc
    rw [mul_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [hXcol l c hc, mul_zero]
  have hBXrow : ∀ r c : Fin N, a ≤ (r : ℕ) → (B * (U - 1)) r c = (U - 1) r c := by
    intro r c hr
    rw [mul_apply, Finset.sum_eq_single r]
    · rw [hB r r (Or.inl hr), if_pos rfl, one_mul]
    · intro l _ hl
      rw [hB r l (Or.inl hr), if_neg (Ne.symm hl), zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ r) hn
  rw [hE]
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hj => ?_, fun i j hi => ?_⟩
  · rw [Matrix.add_apply, one_apply_ne hij.ne']
    by_cases hj : (j : ℕ) < a + 1
    · rw [hBXcol i j hj, add_zero]
    · have hij' : (j : ℕ) < i := hij
      rw [hBXrow i j (by omega), hXlow i j hij.le, add_zero]
  · rw [Matrix.add_apply, one_apply_eq]
    by_cases hi : (i : ℕ) < a + 1
    · rw [hBXcol i i hi, add_zero]
    · rw [hBXrow i i (by omega), hXlow i i le_rfl, add_zero]
  · rw [Matrix.add_apply, hBXcol i j hj, add_zero, one_apply]
  · rw [Matrix.add_apply, hBXrow i j hi, Matrix.sub_apply, add_sub_cancel]

end Conj

section Lvl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_derUnip_iff (N n : ℕ) (u : GL (Fin N) k) :
    u ∈ derUnip k N n ↔ (∀ i j : Fin N, j < i → (u : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      (∀ i : Fin N, (u : Matrix (Fin N) (Fin N) k) i i = 1) ∧
      ∀ i j : Fin N, (j : ℕ) < n → (u : Matrix (Fin N) (Fin N) k) i j = if i = j then 1 else 0 := by
  rw [derUnip, Subgroup.mem_inf, mem_unipB, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  show (∀ j : Fin N, (j : ℕ) < n → (u : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single j 1 = Pi.single j 1) ↔ _
  constructor
  · intro hc i j hj
    have := congrFun (hc j hj) i
    rw [mulVec_single_one] at this
    simpa [Pi.single_apply] using this
  · intro hc j hj
    funext i
    rw [mulVec_single_one]
    simp [Pi.single_apply, hc i j hj]

theorem derUnip_succ_le (N n : ℕ) : derUnip k N (n + 1) ≤ derUnip k N n := by
  intro u hu
  obtain ⟨h1, h2, h3⟩ := (mem_derUnip_iff N (n + 1) u).1 hu
  exact (mem_derUnip_iff N n u).2 ⟨h1, h2, fun i j hj => h3 i j (by omega)⟩

theorem colEl_mem (m N : ℕ) (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : colEl k m N h x ∈ derUnip k N (m + 1) := by
  rw [mem_derUnip_iff]
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hj => ?_⟩
  · have hij' : (j : ℕ) < i := hij
    rw [colEl_val, if_neg (by rw [Fin.ext_iff]; omega)]
    by_cases e1 : (i : ℕ) < m + 1
    · rw [dif_pos e1, if_neg (by omega), add_zero]
    · rw [dif_neg e1, add_zero]
  · rw [colEl_val, if_pos rfl]
    by_cases e1 : (i : ℕ) < m + 1
    · rw [dif_pos e1, if_neg (by omega), add_zero]
    · rw [dif_neg e1, add_zero]
  · rw [colEl_val]
    by_cases e1 : (i : ℕ) < m + 1
    · rw [dif_pos e1, if_neg (show ¬ (j : ℕ) = m + 1 by omega), add_zero]
    · rw [dif_neg e1, add_zero]

theorem lvlChar_apply (ψ : AddChar k Circle) (N n : ℕ) (u : derUnip k N n) :
    lvlChar k ψ N n u = Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n - 1 ≤ (p.1 : ℕ),
      ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2)) := rfl

theorem lvlChar_congr (ψ : AddChar k Circle) (N n : ℕ) (u u' : derUnip k N n)
    (h : ∀ r c : Fin N, n - 1 ≤ (r : ℕ) →
      ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) r c = ((u' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) r c) :
    lvlChar k ψ N n u = lvlChar k ψ N n u' := by
  rw [lvlChar_apply, lvlChar_apply]
  congr 2
  exact Finset.sum_congr rfl fun p hp => h _ _ (Finset.mem_filter.1 hp).2.2

theorem lvlChar_colEl (ψ : AddChar k Circle) (m N : ℕ) (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    lvlChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem m N h x⟩ = Circle.toUnits (ψ (x (Fin.last m))) := by
  rw [lvlChar_apply]
  congr 2
  rw [Finset.sum_eq_single ((⟨m, by omega⟩ : Fin N), (⟨m + 1, by omega⟩ : Fin N))]
  · rw [colEl_val, if_neg (by rw [Fin.ext_iff]; simp), dif_pos (by simp), if_pos rfl, zero_add]
    rfl
  · intro p hp hne
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hp2, hp1⟩ := hp
    rw [colEl_val, if_neg (by rw [Fin.ext_iff]; omega)]
    by_cases e1 : (p.1 : ℕ) < m + 1
    · exfalso
      apply hne
      ext <;> simp <;> omega
    · rw [dif_neg e1, add_zero]
  · intro hn
    exfalso
    apply hn
    simp [Finset.mem_filter]

theorem lvlChar_succ (ψ : AddChar k Circle) (m N : ℕ) (u : GL (Fin N) k) (hu : u ∈ derUnip k N (m + 2)) :
    lvlChar k ψ N (m + 1) ⟨u, derUnip_succ_le N (m + 1) hu⟩ = lvlChar k ψ N (m + 2) ⟨u, hu⟩ := by
  rw [lvlChar_apply, lvlChar_apply]
  congr 2
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, by omega⟩
  · intro p hp hnp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hp hnp
    obtain ⟨_, _, h3⟩ := (mem_derUnip_iff N (m + 2) u).1 hu
    have hp1 : (p.1 : ℕ) = m := by
      by_contra hc
      exact hnp hp.1 (by omega)
    rw [h3 p.1 p.2 (by omega), if_neg (by rw [Fin.ext_iff]; omega)]

theorem twKer_le_succ (ψ : AddChar k Circle) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ) :
    twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) ≤ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨⟨u, hu⟩, v, rfl⟩
  refine Submodule.subset_span ⟨⟨u, derUnip_succ_le N (m + 1) hu⟩, v, ?_⟩
  rw [lvlChar_succ ψ m N u hu]

theorem blkAt_val_out (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (r l : Fin N) (hrl : n ≤ (r : ℕ) ∨ n ≤ (l : ℕ)) :
    ((blkAt k n N h g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) r l = if r = l then 1 else 0 := by
  rw [blkAt_val]
  by_cases hr : (r : ℕ) < n
  · have hl : ¬ (l : ℕ) < n := by omega
    rw [dif_pos hr, dif_neg hl, if_neg (by rw [Fin.ext_iff]; omega)]
  · rw [dif_neg hr]

theorem conj_derUnip (m N : ℕ) (h' : m + 1 ≤ N) (g : GL (Fin (m + 1)) k) (u : GL (Fin N) k)
    (hu : u ∈ derUnip k N (m + 2)) :
    blkAt k (m + 1) N h' g * u * (blkAt k (m + 1) N h' g)⁻¹ ∈ derUnip k N (m + 2) ∧
      ∀ r c : Fin N, m + 1 ≤ (r : ℕ) →
        ((blkAt k (m + 1) N h' g * u * (blkAt k (m + 1) N h' g)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) r c =
          (u : Matrix (Fin N) (Fin N) k) r c := by
  obtain ⟨h1, h2, h3⟩ := (mem_derUnip_iff N (m + 2) u).1 hu
  have hv : ((blkAt k (m + 1) N h' g * u * (blkAt k (m + 1) N h' g)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      ((blkAt k (m + 1) N h' g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) * (u : Matrix (Fin N) (Fin N) k) *
        ((blkAt k (m + 1) N h' g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    rw [Units.val_mul, Units.val_mul, map_inv]
  have hBC : ((blkAt k (m + 1) N h' g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *
      ((blkAt k (m + 1) N h' g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  obtain ⟨k1, k2, k3, k4⟩ := conj_mat N (m + 1) _ _ _ hBC (blkAt_val_out (m + 1) N h' g)
    (blkAt_val_out (m + 1) N h' g⁻¹) h1 h2 (fun i j hj => h3 i j (by omega))
  refine ⟨(mem_derUnip_iff N (m + 2) _).2 ⟨fun i j hij => ?_, fun i => ?_, fun i j hj => ?_⟩, fun r c hr => ?_⟩
  · rw [hv]; exact k1 i j hij
  · rw [hv]; exact k2 i
  · rw [hv]; exact k3 i j (by omega)
  · rw [hv]; exact k4 r c hr

theorem twKer_blkAt (ψ : AddChar k Circle) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ) (h' : m + 1 ≤ N) (g : GL (Fin (m + 1)) k) (y : V)
    (hy : y ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) :
    π (blkAt k (m + 1) N h' g) y ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
  have hle : twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) ≤
      (twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))).comap (π (blkAt k (m + 1) N h' g)) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨⟨u, hu⟩, v, rfl⟩
    obtain ⟨hm, he⟩ := conj_derUnip m N h' g u hu
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.subset_span ⟨⟨_, hm⟩, π (blkAt k (m + 1) N h' g) v, ?_⟩
    rw [lvlChar_congr ψ N (m + 2) ⟨_, hm⟩ ⟨u, hu⟩ (fun r c hr => he r c (by omega)), map_sub, map_smul]
    congr 1
    show π (blkAt k (m + 1) N h' g) (π u v) =
      π (blkAt k (m + 1) N h' g * u * (blkAt k (m + 1) N h' g)⁻¹) (π (blkAt k (m + 1) N h' g) v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  exact hle hy

end Lvl

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_unip (n : ℕ) : Continuous fun x : Fin n → k => unip k n (Multiplicative.ofAdd x) := by
  have hv : ∀ x : Fin n → k, ((unip k n (Multiplicative.ofAdd x) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 + colMat k n x := fun x => rfl
  have hval : Continuous fun x : Fin n → k =>
      ((unip k n (Multiplicative.ofAdd x) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    simp only [hv]
    refine continuous_const.add (continuous_matrix fun i j => ?_)
    simp only [colMat]
    by_cases hj : j = Fin.last n
    · simp only [hj, if_true]
      induction i using Fin.lastCases with
      | last => simpa using continuous_const
      | cast i => simpa using continuous_apply i
    · simpa [hj] using continuous_const
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have e : (fun x : Fin n → k => (((unip k n (Multiplicative.ofAdd x))⁻¹ : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = fun x => ((unip k n (Multiplicative.ofAdd (-x)) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    funext x
    rw [← map_inv, ← ofAdd_neg]
  rw [e]
  exact hval.comp continuous_neg

theorem continuous_blkAt (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  have key : ∀ F : GL (Fin n) k → GL (Fin n) k, Continuous (fun g => ((F g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) →
      Continuous fun g => ((blkAt k n N h (F g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    intro F hF
    refine continuous_matrix fun i j => ?_
    simp only [blkAt_val]
    by_cases hi : (i : ℕ) < n
    · by_cases hj : (j : ℕ) < n
      · simpa [hi, hj] using hF.matrix_elem _ _
      · simpa [hi, hj] using continuous_const
    · simpa [hi] using continuous_const
  refine Units.continuous_iff.2 ⟨key id Units.continuous_val, ?_⟩
  convert key (fun g => g⁻¹) Units.continuous_coe_inv using 2 with g
  simp [map_inv]

theorem continuous_colEl (m N : ℕ) (h : m + 2 ≤ N) : Continuous (colEl k m N h) :=
  (continuous_blkAt (m + 2) N h).comp (continuous_unip (m + 1))

end Top

end PositivityTheory.RgUd.Form.U.Lift2.TrM
