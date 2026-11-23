import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCovSec

open GlobalTheory.NilCov

variable {n : ℕ}

def jInv (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Jm ε * Xᴴ * Jm ε

variable (ε : Fin n → Bool)

theorem jInv_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : jInv ε (X - Y) = jInv ε X - jInv ε Y := by
  simp only [jInv, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem jInv_smul (a : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (a • X) = a • jInv ε X := by
  simp [jInv, conjTranspose_smul]

theorem jInv_jInv_mul (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (jInv ε X * X) = jInv ε X * X := by
  simp only [jInv, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]

theorem continuous_jInv : Continuous (jInv ε) := by
  exact (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

def iter (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Nat.rec Y (fun _ X => Y - (1 / 2 : ℝ) • (jInv ε X * X)) k

theorem continuous_iter (k : ℕ) : Continuous fun Y => iter ε Y k := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    exact continuous_id.sub ((((continuous_jInv ε).comp ih).matrix_mul ih).const_smul (1 / 2 : ℝ))

variable {ε} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}

theorem iter_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y k ∈ A 0 := by
  induction k with
  | zero => exact hY
  | succ k ih =>
    exact (A 0).sub_mem hY ((A 0).smul_mem _ (hle 0 (hmul 0 _ (hinv 0 _ ih) _ ih).1))

theorem iter_sub_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y (k + 1) - iter ε Y k ∈ A k := by
  have hm := iter_mem hmul hle hinv hY
  induction k with
  | zero => exact (A 0).sub_mem (hm 1) (hm 0)
  | succ k ih =>
    have e : iter ε Y (k + 1 + 1) - iter ε Y (k + 1) =
        (-(1 / 2) : ℝ) • (jInv ε (iter ε Y (k + 1) - iter ε Y k) * iter ε Y (k + 1) +
          jInv ε (iter ε Y k) * (iter ε Y (k + 1) - iter ε Y k)) := by
      have e1 : iter ε Y (k + 1 + 1) =
        Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y (k + 1)) * iter ε Y (k + 1)) := rfl
      have e2 : iter ε Y (k + 1) = Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y k) * iter ε Y k) := rfl
      rw [e1]
      generalize iter ε Y (k + 1) = P at e2 ⊢
      generalize iter ε Y k = Q at e2 ⊢
      rw [jInv_sub, Matrix.sub_mul, Matrix.mul_sub]
      nth_rewrite 3 [e2]
      module
    rw [e]
    exact (A _).smul_mem _ ((A _).add_mem (hmul k _ (hinv k _ ih) _ (hm _)).1
      (hmul k _ ih _ (hinv 0 _ (hm _))).2)

theorem one_add_mul_of_fixed {X Y : Matrix (Fin n) (Fin n) ℂ} (hY : jInv ε Y = -Y)
    (h : X = Y - (1 / 2 : ℝ) • (jInv ε X * X)) : (1 + jInv ε X) * (1 + X) = 1 := by
  have h2 : jInv ε X = -Y - (1 / 2 : ℝ) • (jInv ε X * X) := by
    conv_lhs => rw [h]
    rw [jInv_sub, jInv_smul, jInv_jInv_mul, hY]
  have h3 : X + jInv ε X + jInv ε X * X = 0 := by
    generalize jInv ε X * X = P at h h2 ⊢
    rw [h2, h]
    module
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  calc 1 + X + (jInv ε X + jInv ε X * X) = 1 + (X + jInv ε X + jInv ε X * X) := by abel
    _ = 1 := by rw [h3, add_zero]

theorem inUJ_of_one_add_mul {X : Matrix (Fin n) (Fin n) ℂ} (h : (1 + jInv ε X) * (1 + X) = 1) :
    (1 + X)ᴴ * Jm ε * (1 + X) = Jm ε := by
  have e : (1 + X)ᴴ * Jm ε = Jm ε * (1 + jInv ε X) := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, jInv, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  rw [e, Matrix.mul_assoc, h, Matrix.mul_one]

theorem exists_continuous_section (n d m : ℕ) (ε : Fin n → Bool)
    (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hA : A m = ⊥) (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c)
    (hinv : ∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hG : ∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) :
    ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧
      ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  let Y : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => ∑ i, x i • E i
  have hYc : Continuous Y := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const
  have hY0 : ∀ x, Y x ∈ A 0 := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hG i).1
  have hYθ : ∀ x, jInv ε (Y x) = -Y x := fun x => by
    simp only [jInv, Y, conjTranspose_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := jInv_smul ε (x i) (E i)
    unfold jInv at this
    rw [this, inv_eq_neg_of_inG (hG i).2, smul_neg]
  let X : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => iter ε (Y x) m
  have hXc : Continuous X := (continuous_iter ε m).comp hYc
  have hfix : ∀ x, X x = Y x - (1 / 2 : ℝ) • (jInv ε (X x) * X x) := fun x => by
    have h := iter_sub_mem hmul hle hinv (hY0 x) m
    rw [hA, Submodule.mem_bot, sub_eq_zero] at h
    exact h.symm
  have h1 : ∀ x, (1 + jInv ε (X x)) * (1 + X x) = 1 := fun x => one_add_mul_of_fixed (hYθ x) (hfix x)
  let u : (Fin d → ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun x =>
    ⟨1 + X x, 1 + jInv ε (X x), mul_eq_one_comm.1 (h1 x), h1 x⟩
  have huc : Continuous u := Units.continuous_iff.2
    ⟨continuous_const.add hXc, continuous_const.add ((continuous_jInv ε).comp hXc)⟩
  have hu : ∀ x, u x ∈ UJ ε := fun x => inUJ_of_one_add_mul (h1 x)
  refine ⟨fun x => ⟨u x, hu x⟩, huc.subtype_mk hu, fun x => ?_⟩
  have e : uMat (⟨u x, hu x⟩ : UJ ε) - 1 = X x := by
    change 1 + X x - 1 = X x
    abel
  rw [e]
  refine ⟨iter_mem hmul hle hinv (hY0 x) m, fun i => ?_⟩
  have h0 : ipL (E i) (jInv ε (X x) * X x) = 0 := by
    have h := ipL_inv (hG i).2 (jInv ε (X x) * X x)
    have h' : ipL (E i) (jInv ε (jInv ε (X x) * X x)) = -ipL (E i) (jInv ε (X x) * X x) := h
    rw [jInv_jInv_mul] at h'
    linarith
  rw [← ipL_apply, hfix x, map_sub, map_smul, h0, smul_zero, sub_zero]
  simp only [Y, map_sum, map_smul, ipL_apply, hE, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

end GlobalTheory.NilCovSec
