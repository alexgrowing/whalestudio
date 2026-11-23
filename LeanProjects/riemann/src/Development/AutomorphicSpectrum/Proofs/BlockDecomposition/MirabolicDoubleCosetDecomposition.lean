import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Cells

section Alg

variable {k : Type} [Field k]

theorem exists_row {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Prop) (ρ : ι → k) (c j : ι)
    (hc : ρ c ≠ 0) (hcj : s c ↔ s j) (hρ : ¬ s j → ∀ x, s x → ρ x = 0) :
    ∃ B : GL ι k, (B : Matrix ι ι k) j = ρ ∧ ∀ r x, ¬ s r → s x → (B : Matrix ι ι k) r x = 0 := by
  let T : Matrix ι ι k := (1 : Matrix ι ι k).updateRow c ρ
  let M : Matrix ι ι k := T.submatrix (Equiv.swap c j) id
  have hT : T.det = ρ c := by
    have h := Matrix.cramer_transpose_apply (1 : Matrix ι ι k) ρ c
    rw [Matrix.transpose_one, Matrix.cramer_one] at h
    simpa using h.symm
  have hdet : M.det ≠ 0 := by
    have h := Matrix.det_permute (Equiv.swap c j) T
    have h2 : M.det = _ := h
    rw [h2, hT]
    refine mul_ne_zero ?_ hc
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap c j)) with e | e <;> simp [e]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · ext x
    show T (Equiv.swap c j j) x = ρ x
    simp [T]
  · intro r x hr hx
    show T (Equiv.swap c j r) x = 0
    by_cases hrj : r = j
    · subst hrj
      simpa [T] using hρ hr x hx
    · have hne : Equiv.swap c j r ≠ c := by
        intro e
        exact hrj (by simpa using congrArg (Equiv.swap c j) e)
      simp only [T, Matrix.updateRow_ne hne, Matrix.one_apply]
      rw [if_neg]
      intro e
      by_cases hrc : r = c
      · subst hrc
        simp at e
        subst e
        exact hr (hcj.2 hx)
      · rw [Equiv.swap_apply_of_ne_of_ne hrc hrj] at e
        subst e
        exact hr hx

theorem eq_unip_glEmb {n : ℕ} (p : Mir k n) :
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

theorem unip_castSucc_castSucc (n : ℕ) (v : Fin n → k) (r c : Fin n) (h : r ≠ c) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.castSucc r) (Fin.castSucc c) = 0 := by
  show (1 + colMat k n v) _ _ = 0
  simp [colMat, Matrix.one_apply, h, Fin.castSucc_ne_last]

theorem glEmb_castSucc_castSucc (n : ℕ) (g : GL (Fin n) k) (r c : Fin n) :
    (glEmb k n g).val (Fin.castSucc r) (Fin.castSucc c) = g.val r c := by
  show glEmbMat k n g.val _ _ = _
  simp [glEmbMat]

theorem glEmb_castSucc_last (n : ℕ) (g : GL (Fin n) k) (r : Fin n) :
    (glEmb k n g).val (Fin.castSucc r) (Fin.last n) = 0 := by
  show glEmbMat k n g.val _ _ = _
  simp [glEmbMat]

theorem ePG_true_val (I T : ℕ) (x : Fin T) : (ePG I T ⟨true, x⟩ : Fin (I + T + 1)).val = I + x := by
  simp [ePG, two]

theorem ePG_false_val (I T : ℕ) (y : Fin I) : (ePG I T ⟨false, Fin.castSucc y⟩ : Fin (I + T + 1)).val = y := by
  simp [ePG, two, finSumFinEquiv_symm_apply_castSucc]

end Alg

section Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_HPG_of {I T : ℕ} (g : Mir k (I + T))
    (h : ∀ (x : Fin T) (y : Fin I), (g : GL (Fin (I + T + 1)) k).val
        (Fin.castSucc (⟨I + x, by omega⟩ : Fin (I + T))) (Fin.castSucc (⟨y, by omega⟩ : Fin (I + T))) = 0)
    (h' : ∀ x : Fin T, (g : GL (Fin (I + T + 1)) k).val
        (Fin.castSucc (⟨I + x, by omega⟩ : Fin (I + T))) (Fin.last (I + T)) = 0) :
    g ∈ HPG k I T := by
  show (g : GL (Fin (I + T + 1)) k) ∈ parab k (ePG I T)
  refine mem_parab_iff.2 ?_
  rintro (_ | _) (_ | _) a b hab
  · exact absurd hab (by decide)
  · exact absurd hab (by decide)
  · have ea : ePG I T ⟨true, a⟩ = Fin.castSucc ⟨I + a.1, by have := a.2; change a.1 < T at this; omega⟩ :=
      Fin.ext (ePG_true_val I T a)
    induction b using Fin.lastCases with
    | last =>
      rw [ea, ePG_false_last]
      exact h' a
    | cast y =>
      have eb : ePG I T ⟨false, Fin.castSucc y⟩ = Fin.castSucc ⟨y, by omega⟩ := Fin.ext (ePG_false_val I T y)
      rw [ea, eb]
      exact h a y
  · exact absurd hab (by decide)

theorem core (i t : ℕ) (p : Mir k ((i + 1) + t + 1)) (X B : GL (Fin ((i + 1) + t + 1)) k) (j : Fin ((i + 1) + t + 1))
    (hX : X.val j = eLast k ((i + 1) + t))
    (hBj : B.val j = (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t)))
    (hB : ∀ r x : Fin ((i + 1) + t + 1), ¬ r.val < i + 1 → x.val < i + 1 → B.val r x = 0) :
    ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * levi k _ X * sEmb k ((i + 1) + t) m := by
  set g : GL (Fin ((i + 1) + t + 1)) k := mirabolicProjection k _ p with hg
  have hginv : mirabolicProjection k _ p⁻¹ = g⁻¹ := map_inv _ _
  rw [hginv] at hBj
  have hM : (X⁻¹ * B * g) ∈ Mir k ((i + 1) + t) := by
    have h1 : (g⁻¹ * (B⁻¹ * X)) ∈ Mir k ((i + 1) + t) := by
      rw [mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, ← hBj, ← Matrix.mul_apply_eq_vecMul, ← Units.val_mul,
        mul_inv_cancel_left, hX]
    have h2 := (Mir k ((i + 1) + t)).inv_mem h1
    simpa [mul_assoc] using h2
  let v : Fin ((i + 1) + (t + 1)) → k := fun r =>
    (p : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc r) (Fin.last _)
  let v' : Fin ((i + 1) + (t + 1)) → k := B.val.mulVec v
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append (fun x => v' (Fin.castAdd (t + 1) x)) (0 : Fin (t + 1) → k)
  let d : Fin (t + 1) → k := fun x => v' (Fin.natAdd (i + 1) x)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  have hsum : a + b = v' := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b]
    | right x => simp [a, b, d]
  have hp := eq_unip_glEmb p
  let ua : Mir k ((i + 1) + t + 1) := ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd a), MirU_le_Mir k _ ⟨_, rfl⟩⟩
  have hua : ua ∈ HPG k (i + 1) (t + 1) := by
    refine mem_HPG_of (I := i + 1) (T := t + 1) ua ?_ ?_
    · intro x y
      refine unip_castSucc_castSucc _ a _ _ ?_
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    · intro x
      refine (unip_apply_castSucc_last k _ _ _).trans ?_
      show a (Fin.natAdd (i + 1) x) = 0
      simp [a]
  have hlB : levi k _ B⁻¹ ∈ HPG k (i + 1) (t + 1) := by
    have : levi k _ B ∈ HPG k (i + 1) (t + 1) := by
      refine mem_HPG_of (I := i + 1) (T := t + 1) _ ?_ ?_
      · intro x y
        refine (glEmb_castSucc_castSucc _ B _ _).trans ?_
        exact hB _ _ (by simp; omega) (by simp; omega)
      · intro x
        exact glEmb_castSucc_last _ B _
    rw [map_inv]
    exact (HPG k (i + 1) (t + 1)).inv_mem this
  refine ⟨levi k _ B⁻¹ * ua, (HPG k (i + 1) (t + 1)).mul_mem hlB hua, d, ⟨_, hM⟩, ?_⟩
  apply Subtype.ext
  have hp : (p : GL (Fin ((i + 1) + t + 1 + 1)) k) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ g := eq_unip_glEmb p
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e2 : glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * glEmb k _ B := glEmb_mul_unip' k _ B _
  have e3 : glEmb k _ X * glEmb k _ (X⁻¹ * B * g) = glEmb k _ B * glEmb k _ g := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  show (p : GL (Fin ((i + 1) + t + 1 + 1)) k) = glEmb k _ B⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) *
      glEmb k _ X * glEmb k _ (X⁻¹ * B * g)
  calc (p : GL (Fin ((i + 1) + t + 1 + 1)) k)
      = (glEmb k _ B)⁻¹ * (glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v)) * glEmb k _ g := by
        rw [hp]; group
    _ = (glEmb k _ B)⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * (glEmb k _ B * glEmb k _ g) := by
        rw [e2]; simp only [mul_assoc]
    _ = _ := by
        rw [← e3, ← e1, map_inv]; simp only [mul_assoc]

theorem row_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι k) (r : ι) : ∃ c, g.val r c ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h0 := Matrix.det_eq_zero_of_row_eq_zero r hc
  exact (Matrix.GeneralLinearGroup.det g).ne_zero (by simpa using h0)

theorem piPerm_last_val (i t : ℕ) : (piPerm i t (Fin.last ((i + 1) + t))).val = i := by
  have e : (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)) (Fin.last ((i + 1) + t)) = ePG i (t + 1) ⟨false, Fin.last i⟩ := by
    rw [ePG_false_last]
    apply Fin.ext
    simp
  show (eGP (i + 1) t ((ePG i (t + 1)).symm ((finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)) (Fin.last ((i + 1) + t))))).val = i
  rw [e, Equiv.symm_apply_apply]
  simp [eGP, two, stdSum]

theorem wGL_row (i t : ℕ) : (wGL k i t).val (piPerm i t (Fin.last ((i + 1) + t))) = eLast k ((i + 1) + t) := by
  funext b
  show Equiv.Perm.permMatrix k (piPerm i t)⁻¹ _ b = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eLast, Pi.single_apply, eq_comm]

theorem Cl_iff (i t : ℕ) (p : Mir k ((i + 1) + t + 1)) : p ∈ Cl k i t ↔ ∀ c : Fin ((i + 1) + t + 1), c.val < i + 1 →
    (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t)) c = 0 := by
  constructor
  · intro h c hc
    exact h ⟨c.val, hc⟩
  · intro h c
    exact h (Fin.castLE (by omega) c) c.2

theorem cells :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ),
  (∀ p ∈ Cl k i t, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * sEmb k ((i + 1) + t) m) ∧
  (∀ p, p ∉ Cl k i t → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) := by
  intro k _ _ _ _ i t
  constructor
  · intro p hp
    have hp' := (Cl_iff i t p).1 hp
    obtain ⟨c, hc⟩ := row_ne_zero (mirabolicProjection k _ p⁻¹) (Fin.last ((i + 1) + t))
    have hlast : ¬ (Fin.last ((i + 1) + t)).val < i + 1 := by simp; omega
    have hcs : ¬ c.val < i + 1 := fun h => hc (hp' c h)
    obtain ⟨B, hBj, hB⟩ := exists_row (fun x : Fin ((i + 1) + t + 1) => x.val < i + 1) _ c (Fin.last ((i + 1) + t)) hc
      (by simp only [hcs, hlast]) (fun _ x hx => hp' x hx)
    obtain ⟨h, hh, d, m, e⟩ := core i t p 1 B (Fin.last ((i + 1) + t)) (by funext b; simp [eLast, Matrix.one_apply, Pi.single_apply, eq_comm]) hBj hB
    exact ⟨h, hh, d, m, by simpa using e⟩
  · intro p hp
    have hp' : ¬ _ := fun h => hp ((Cl_iff i t p).2 h)
    push_neg at hp'
    obtain ⟨c, hcs, hc⟩ := hp'
    have hj : (piPerm i t (Fin.last ((i + 1) + t))).val < i + 1 := by rw [piPerm_last_val]; omega
    obtain ⟨B, hBj, hB⟩ := exists_row (fun x : Fin ((i + 1) + t + 1) => x.val < i + 1) _ c (piPerm i t (Fin.last ((i + 1) + t))) hc
      (by simp only [hcs, hj]) (fun h => absurd hj h)
    exact core i t p (wGL k i t) B _ (wGL_row i t) hBj hB

end Group

end GlobalTheory.CompanionTheory.BZPhiPG.Cells

end
