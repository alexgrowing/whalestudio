import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Closed

open GlobalTheory.CompanionTheory.BZPhiPhi

section LinAlg

variable {k : Type} [Field k]

theorem exists_GL_row (N m : ℕ) (r : Fin (N + 1) → k) (hr0 : ∀ l : Fin (N + 1), l.val < m → r l = 0)
    (hr : r ≠ 0) :
    ∃ A : GL (Fin (N + 1)) k, (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) (Fin.last N) = r ∧
      ∀ i l : Fin (N + 1), m ≤ i.val → l.val < m → (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) i l = 0 := by
  classical
  obtain ⟨l0, hl0⟩ : ∃ l, r l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  have hml : m ≤ l0.val := by
    by_contra h
    exact hl0 (hr0 l0 (by omega))
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) k := (1 : Matrix _ _ k).updateRow l0 r
  have hB : B.det = r l0 := by
    have h1 := Matrix.cramer_apply (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k) r l0
    rw [Matrix.cramer_one] at h1
    have h2 := Matrix.updateRow_transpose (M := (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k)) (j := l0) (c := r)
    rw [Matrix.transpose_one] at h2
    show ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k).updateRow l0 r).det = r l0
    rw [h2, Matrix.det_transpose, ← h1]
    rfl
  let σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap l0 (Fin.last N)
  let A : Matrix (Fin (N + 1)) (Fin (N + 1)) k := B.submatrix σ id
  have hA : A.det ≠ 0 := by
    have : A.det = _ := Matrix.det_permute σ B
    rw [this, hB]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hl0]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, ?_, ?_⟩
  · funext l
    show B (σ (Fin.last N)) l = r l
    simp [σ, B]
  · intro i l hi hl
    show B (σ i) l = 0
    have hs : m ≤ (σ i).val := by
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · have := Fin.is_lt l
        have h3 : l0.val ≤ N := by omega
        simp only [Fin.val_last]
        omega
      · exact hml
      · exact hi
    simp only [B, Matrix.updateRow_apply]
    split_ifs
    · exact hr0 l hl
    · rw [Matrix.one_apply_ne]
      intro e
      rw [e] at hs
      omega

theorem levi_val (n : ℕ) (A : GL (Fin n) k) :
    (((levi k n A : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (A : Matrix (Fin n) (Fin n) k) := rfl

theorem mirProj_val (n : ℕ) (g : Mir k n) (i l : Fin n) :
    ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc l) := rfl

theorem glEmbMat_last_cast (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (l : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc l) = 0 := by
  simp [glEmbMat]

theorem mirProj_levi_eq (n : ℕ) (A : GL (Fin n) k) : mirabolicProjection k n (levi k n A) = A := by
  ext i l
  rw [mirProj_val, levi_val]
  simp [glEmbMat]

theorem rowQ_ne_zero (n : ℕ) (p : Mir k (n + 1)) : rowQ k n p ≠ 0 := by
  intro h
  have key : vecMul (eLast k n) ((mirabolicProjection k (n + 1) p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      rowQ k n p := by
    rw [vecMul_eLast]
    rfl
  have h2 : eLast k n = 0 := by
    have h3 := congrArg (fun v => vecMul v ((((mirabolicProjection k (n + 1) p)⁻¹ : GL (Fin (n + 1)) k)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k)) key
    simp only [h, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h3
    exact h3
  have h4 := congrFun h2 (Fin.last n)
  simp [eLast] at h4

theorem entry_of_mirProj_eq_one (n : ℕ) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (i l : Fin (n + 1))
    (hil : i ≠ l) (hl : l ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l = 0 := by
  obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl
  induction i using Fin.lastCases with
  | last =>
    rw [(mem_Mir_iff k _).1 u.2]
    simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  | cast i =>
    rw [← mirProj_val, hu]
    have : i ≠ l' := fun e => hil (by rw [e])
    simp [Matrix.one_apply, this]

theorem row_levi (n : ℕ) (y : Mir k n) (t : Fin (n + 2)) :
    (((levi k (n + 1) (y : GL (Fin (n + 1)) k) : Mir k (n + 1)) : GL (Fin (n + 2)) k) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t =
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t := by
  rw [levi_val]
  have hy := (mem_Mir_iff k _).1 y.2
  induction t using Fin.lastCases with
  | last => simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last]
  | cast t =>
    simp only [glEmbMat, Fin.lastCases_castSucc]
    rw [hy]
    by_cases h : t = Fin.last n
    · subst h; simp [eLast]
    · have : (Fin.last n) ≠ t := fun e => h e.symm
      simp [eLast, Pi.single_apply, h, Matrix.one_apply, this]

end LinAlg

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_mirabolicParabolic_iff_lt (m j : ℕ) (g : Mir k (m + (j + 1))) :
    g ∈ MirabolicParabolic k m (j + 1) ↔ ∀ i l : Fin (m + (j + 1) + 1), m ≤ i.val → l.val < m →
      ((g : GL (Fin (m + (j + 1) + 1)) k) : Matrix (Fin (m + (j + 1) + 1)) (Fin (m + (j + 1) + 1)) k) i l = 0 := by
  rw [mem_mirabolicParabolic_iff]
  constructor
  · intro h i l hi hl
    have hb : i.val - m < j + 1 + 1 := by have := i.2; omega
    have h1 := h ⟨i.val - m, hb⟩ ⟨l.val, hl⟩
    have e1 : eGP m (j + 1) ⟨true, ⟨i.val - m, hb⟩⟩ = i := Fin.ext (by rw [blockIndex_true_val]; simp; omega)
    have e2 : eGP m (j + 1) ⟨false, ⟨l.val, hl⟩⟩ = l := Fin.ext (by rw [blockIndex_false_val])
    rwa [e1, e2] at h1
  · intro h b a
    apply h
    · rw [blockIndex_true_val]; omega
    · rw [blockIndex_false_val]; exact a.2

theorem set_eq (m j : ℕ) :
    {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} =
      {g | ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0} := by
  ext g
  constructor
  · rintro ⟨h, hh, x, rfl⟩ l hl
    have e : (h * embedding₂ k (m + j) x)⁻¹ = embedding₂ k (m + j) x⁻¹ * h⁻¹ := by
      rw [_root_.mul_inv_rev, map_inv]
    rw [e]
    have hi := (mem_mirabolicParabolic_iff_lt k m j h⁻¹).1 (inv_mem hh)
    show ((embedding₂ k (m + j) x⁻¹).1.1 * (h⁻¹ : Mir k (m + j + 1)).1.1)
        (Fin.castSucc (Fin.last (m + j))) (Fin.castSucc l) = 0
    rw [Matrix.mul_apply]
    simp only [embedding₂, MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [row_levi, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hi _ _ (by simp) (by simpa using hl)
  · intro hg
    obtain ⟨A, hA1, hA2⟩ := exists_GL_row (m + j) m (rowQ k (m + j) g⁻¹) hg (rowQ_ne_zero _ _)
    let d : Mir k (m + (j + 1)) := levi k (m + j + 1) A
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      have hl' : l ≠ Fin.last (m + j + 1) := by
        intro e; rw [e] at hl; simp at hl; omega
      obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl'
      show (levi k (m + j + 1) A).1.1 i _ = 0
      rw [levi_val]
      induction i using Fin.lastCases with
      | last => exact glEmbMat_last_cast _ _ _
      | cast i =>
        simp only [glEmbMat, Fin.lastCases_castSucc]
        exact hA2 i l' (by simpa using hi) (by simpa using hl)
    have rd : rowQ k (m + j) d = rowQ k (m + j) g⁻¹ := by
      funext l
      have : rowQ k (m + j) d l = (A : Matrix _ _ k) (Fin.last (m + j)) l := by
        show (levi k (m + j + 1) A).1.1 _ _ = _
        rw [levi_val]
        simp [glEmbMat]
      rw [this, hA1]
    have hq : g⁻¹ * d⁻¹ ∈ Q k (m + j) := mul_inv_mem_Q_of_rowQ_eq _ _ _ rd.symm
    have hq' : (g⁻¹ * d⁻¹)⁻¹ ∈ Q k (m + j) := inv_mem hq
    let y : Mir k (m + j) := ⟨mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹, hq'⟩
    let u : Mir k (m + j + 1) := (g⁻¹ * d⁻¹)⁻¹ * (embedding₂ k (m + j) y)⁻¹
    have hu : mirabolicProjection k (m + j + 1) u = 1 := by
      simp only [u, map_mul, map_inv (mirabolicProjection k (m + j + 1)) (embedding₂ k (m + j) y)]
      have : mirabolicProjection k (m + j + 1) (embedding₂ k (m + j) y) = mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹ :=
        mirProj_levi_eq _ _
      rw [this]
      simp
    have huH : u ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      refine entry_of_mirProj_eq_one _ u hu i l ?_ ?_
      · intro e; rw [e] at hi; omega
      · intro e; rw [e] at hl; simp at hl; omega
    refine ⟨d⁻¹ * u, mul_mem (inv_mem hd) huH, y, ?_⟩
    simp only [u]
    group

theorem isClosed_HGP_iota (m j : ℕ) :
    IsClosed {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  rw [set_eq]
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun l => isClosed_iInter fun _ =>
    isClosed_eq (((continuous_apply l).comp (continuous_rowQ (m + j))).comp continuous_inv) continuous_const

end Conc

end GlobalTheory.CompanionTheory.LeibPhi.Closed

end
