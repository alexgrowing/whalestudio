import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Conj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unip_cc (n : ℕ) (v : Fin n → k) (r c : Fin n) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.castSucc r) (Fin.castSucc c) = (1 : Matrix (Fin n) (Fin n) k) r c := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem unip_lc (n : ℕ) (v : Fin n → k) (c : Fin n) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.last n) (Fin.castSucc c) = 0 := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem unip_ll (n : ℕ) (v : Fin n → k) :
    (unip k n (Multiplicative.ofAdd v)).val (Fin.last n) (Fin.last n) = 1 := by
  show (1 + colMat k n v) _ _ = _
  simp [colMat]

theorem unip_mul_glEmb (n : ℕ) (g : GL (Fin n) k) (a b c : Fin n → k)
    (h : ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec a = b + c) :
    unip k n (Multiplicative.ofAdd a) * glEmb k n g =
      glEmb k n g * unip k n (Multiplicative.ofAdd b) * unip k n (Multiplicative.ofAdd c) := by
  rw [mul_assoc, ← map_mul, ← ofAdd_add, ← h, glEmb_mul_unip']
  simp only [toAdd_ofAdd]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem castM_val {a b : ℕ} (h : a = b) (m : Mir k a) (x y : Fin (b + 1)) :
    ((castM k h m : Mir k b) : GL (Fin (b + 1)) k).val x y =
      (m : GL (Fin (a + 1)) k).val (Fin.cast (by omega) x) (Fin.cast (by omega) y) := by
  subst h
  rfl

def eps (i t : ℕ) : (Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) ≃ Fin ((i + 1) + t + 1) :=
  (ePG i (t + 1)).trans (finCongr (by omega))

theorem piPerm_eps (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    piPerm i t (eps i t s) = eGP (i + 1) t s := by
  simp [piPerm, eps]

theorem blockIndex_true (i t : ℕ) (y : Fin (t + 1)) : eGP (i + 1) t ⟨true, y⟩ = Fin.natAdd (i + 1) y :=
  Fin.ext (by simp [eGP, two, stdSum])

theorem blockIndex_false (i t : ℕ) (a : Fin (i + 1)) : eGP (i + 1) t ⟨false, a⟩ = Fin.castAdd (t + 1) a :=
  Fin.ext (by simp [eGP, two, stdSum])

def gEl (i t : ℕ) (m : Mir k (i + (t + 1))) : GL (Fin ((i + 1) + t + 1)) k :=
  wGL k i t * ((castM k (by omega) m : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹

theorem gEl_inv (i t : ℕ) (m : Mir k (i + (t + 1))) : (gEl i t m)⁻¹ = gEl i t m⁻¹ := by
  simp [gEl, mul_assoc, map_inv]

theorem wGL_conj_mulVec (i t : ℕ) (M : GL (Fin ((i + 1) + t + 1)) k) (u : Fin ((i + 1) + t + 1) → k)
    (a : Fin ((i + 1) + t + 1)) :
    ((wGL k i t * M * (wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val.mulVec u) (piPerm i t a) =
      (M.val.mulVec (u ∘ piPerm i t)) a := by
  show ((Equiv.Perm.permMatrix k (piPerm i t)⁻¹ * M.val * Equiv.Perm.permMatrix k (piPerm i t)).mulVec u) (piPerm i t a) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec, Matrix.permMatrix_mulVec]
  simp [Function.comp]

theorem gEl_mulVec (i t : ℕ) (m : Mir k (i + (t + 1))) (u : Fin ((i + 1) + t + 1) → k)
    (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    ((gEl i t m).val.mulVec u) (eGP (i + 1) t s) =
      (∑ x : Fin (i + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨false, x⟩) *
        u (eGP (i + 1) t ⟨false, x⟩)) +
      ∑ y : Fin (t + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨true, y⟩) *
        u (eGP (i + 1) t ⟨true, y⟩) := by
  rw [← piPerm_eps, gEl, wGL_conj_mulVec]
  show (∑ b : Fin ((i + 1) + t + 1), (_ : k)) = _
  rw [← Equiv.sum_comp (eps i t), Fintype.sum_sigma, Fintype.sum_bool, add_comm]
  simp only [Function.comp, piPerm_eps]
  congr 1
  all_goals exact Finset.sum_congr rfl fun x _ => by rw [castM_val]; rfl

theorem ePG_true_ne_last (i t : ℕ) (y : Fin (t + 1)) : ePG i (t + 1) ⟨true, y⟩ ≠ Fin.last (i + (t + 1)) := by
  intro e
  have h1 := congrArg Fin.val e
  rw [Cells.ePG_true_val] at h1
  have := y.2
  simp only [Fin.val_last] at h1
  change y.1 < t + 1 at this
  omega

theorem ePG_false_castSucc' (i t : ℕ) (y : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc y⟩ = Fin.castSucc (Fin.castAdd (t + 1) y) :=
  Fin.ext (by simpa using Cells.ePG_false_val (i + 1) (t + 1) y)

theorem ePG_true' (i t : ℕ) (y : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, y⟩ = Fin.castSucc (Fin.natAdd (i + 1) y) :=
  Fin.ext (by simpa using Cells.ePG_true_val (i + 1) (t + 1) y)

abbrev uD (i t : ℕ) (d : Fin (t + 1) → k) : Fin ((i + 1) + t + 1) → k := @Fin.append (i + 1) (t + 1) k 0 d

theorem gEl_uD (i t : ℕ) (m : Mir k (i + (t + 1))) (d : Fin (t + 1) → k)
    (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    ((gEl i t m).val.mulVec (uD i t d)) (eGP (i + 1) t s) =
      ∑ y : Fin (t + 1), (m : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) ⟨true, y⟩) * d y := by
  rw [gEl_mulVec, Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [blockIndex_true]
    congr 1
    exact Fin.append_right _ _ y
  · intro x _
    rw [blockIndex_false]
    have : uD i t d (Fin.castAdd (t + 1) x) = 0 := Fin.append_left _ _ x
    rw [this, mul_zero]

theorem vec_last (i t : ℕ) (m : Mir k (i + (t + 1))) (d : Fin (t + 1) → k) :
    ((gEl i t m).val.mulVec (uD i t d)) (Fin.castAdd (t + 1) (Fin.last i)) = 0 := by
  have h := gEl_uD i t m d ⟨false, Fin.last i⟩
  rw [blockIndex_false, ePG_false_last] at h
  refine h.trans (Finset.sum_eq_zero fun y _ => ?_)
  have hm := (mem_Mir_iff k (m : GL (Fin (i + (t + 1) + 1)) k)).1 m.2
  rw [hm]
  simp [eLast, Pi.single_apply, ePG_true_ne_last]

theorem vec_true (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k) (y : Fin (t + 1)) :
    ((gEl i t (h : Mir k (i + (t + 1)))⁻¹).val.mulVec (uD i t d)) (Fin.natAdd (i + 1) y) =
      ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) y := by
  have h1 := gEl_uD i t (h : Mir k (i + (t + 1)))⁻¹ d ⟨true, y⟩
  rw [blockIndex_true] at h1
  refine h1.trans ?_
  have e : ((pgProj k i (t + 1) h).2)⁻¹ = (pgProj k i (t + 1) h⁻¹).2 := by
    rw [map_inv]; rfl
  rw [e]
  rfl

def cEl (i t : ℕ) (x : Fin (i + 1) → k) : Mir k ((i + 1) + (t + 1)) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k))), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem cEl_mem (i t : ℕ) (x : Fin (i + 1) → k) : cEl i t x ∈ HPG k (i + 1) (t + 1) := by
  refine Cells.mem_HPG_of (I := i + 1) (T := t + 1) (cEl i t x) ?_ ?_
  · intro a b
    refine Cells.unip_castSucc_castSucc _ _ _ _ ?_
    intro e
    have := congrArg Fin.val e
    simp only at this
    omega
  · intro a
    refine (unip_apply_castSucc_last k _ _ _).trans ?_
    show Fin.append x (0 : Fin (t + 1) → k) (Fin.natAdd (i + 1) a) = 0
    simp

def uEl (i : ℕ) (x : Fin (i + 1) → k) : MirUin k (i + 1) :=
  ⟨⟨unip k (i + 1) (Multiplicative.ofAdd x), MirU_le_Mir k _ ⟨_, rfl⟩⟩, ⟨_, rfl⟩⟩

theorem pgProj_cEl (i t : ℕ) (x : Fin (i + 1) → k) :
    pgProj k (i + 1) (t + 1) ⟨cEl i t x, cEl_mem i t x⟩ = ((uEl i x : Mir k (i + 1)), 1) := by
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k)))).val
      (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
      (unip k (i + 1) (Multiplicative.ofAdd x)).val a b
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, unip_ll, unip_ll]
      | cast b => rw [ePG_false_castSucc', unip_lc, unip_lc]
    | cast a =>
      rw [ePG_false_castSucc']
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last, unip_apply_castSucc_last, unip_apply_castSucc_last]
        simp
      | cast b =>
        rw [ePG_false_castSucc', unip_cc, unip_cc]
        simp [Matrix.one_apply]
  · apply Units.ext
    ext a b
    show (unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append x (0 : Fin (t + 1) → k)))).val
      (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
    rw [ePG_true', ePG_true', unip_cc]
    simp [Matrix.one_apply]

theorem conj_eq_levi (i t : ℕ) (m : Mir k (i + (t + 1))) :
    wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) m) * (wEl k i t)⁻¹ = levi k _ (gEl i t m) := by
  rw [gEl, map_mul, map_mul, map_inv]
  rfl

theorem dEmb_conj :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k),
  ∃ (c : HPG k (i + 1) (t + 1)) (u : MirUin k (i + 1)),
    pgProj k (i + 1) (t + 1) c = ((u : Mir k (i + 1)), 1) ∧ mirChar k ψ i u = 1 ∧
    dEmb k i t d * (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) =
      (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) * (c : Mir k ((i + 1) + (t + 1))) *
        dEmb k i t ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := by
  intro k _ _ _ _ ψ i t h d
  let v : Fin ((i + 1) + t + 1) → k := (gEl i t (h : Mir k (i + (t + 1)))⁻¹).val.mulVec (uD i t d)
  let x : Fin (i + 1) → k := fun a => v (Fin.castAdd (t + 1) a)
  refine ⟨⟨cEl i t x, cEl_mem i t x⟩, uEl i x, pgProj_cEl i t x, ?_, ?_⟩
  · rw [mirChar_eq k ψ i (uEl i x) (Multiplicative.ofAdd x) rfl]
    have hx : x (Fin.last i) = 0 := vec_last i t _ d
    simp [hx]
  · rw [conj_eq_levi]
    apply Subtype.ext
    refine unip_mul_glEmb ((i + 1) + t + 1) (gEl i t (h : Mir k (i + (t + 1)))) _ _ _ ?_
    rw [gEl_inv]
    have key : ∀ z : Fin ((i + 1) + (t + 1)), v z = @Fin.append (i + 1) (t + 1) k x 0 z +
        @Fin.append (i + 1) (t + 1) k 0 ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) z := by
      intro z
      induction z using Fin.addCases with
      | left a => rw [Fin.append_left, Fin.append_left, Pi.zero_apply, add_zero]
      | right y =>
        rw [Fin.append_right, Fin.append_right, Pi.zero_apply, zero_add]
        exact vec_true i t h d y
    exact funext key

end GlobalTheory.CompanionTheory.BZPhiPG.Conj

end
