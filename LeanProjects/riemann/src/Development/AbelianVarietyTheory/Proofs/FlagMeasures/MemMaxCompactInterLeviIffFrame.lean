import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagLeviRange

variable {n a : ℕ} {j : Fin a → ℕ}

noncomputable def proj (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (l : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i ∈ univ.filter (fun i : Fin a => i.val < l), T i * (T i)ᴴ

theorem proj_conjTranspose (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (l : ℕ) : (proj T l)ᴴ = proj T l := by
  unfold proj
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem proj_mul (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (k : Fin a) (hk : k.val < l) :
    proj T l * T k = T k := by
  unfold proj
  rw [Matrix.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro i _ hik
    rw [Matrix.mul_assoc, h2 i k hik, Matrix.mul_zero]
  · intro hk'
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩) hk'

theorem proj_keep (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (hA : ∀ i, A * T i = T i * c i) :
    proj T l * (A * proj T l) = A * proj T l := by
  have e : A * proj T l = ∑ i ∈ univ.filter (fun i : Fin a => i.val < l), T i * c i * (T i)ᴴ := by
    unfold proj
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Matrix.mul_assoc, hA i]
  rw [e, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, proj_mul T h1 h2 l i (Finset.mem_filter.1 hi).2]

theorem proj_idem (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) : proj T l * proj T l = proj T l := by
  calc proj T l * proj T l
      = proj T l * ∑ k ∈ univ.filter (fun i : Fin a => i.val < l), T k * (T k)ᴴ := rfl
    _ = ∑ k ∈ univ.filter (fun i : Fin a => i.val < l), proj T l * T k * (T k)ᴴ := by
        rw [Matrix.mul_sum]
        simp only [Matrix.mul_assoc]
    _ = ∑ k ∈ univ.filter (fun i : Fin a => i.val < l), T k * (T k)ᴴ :=
        Finset.sum_congr rfl fun k hk => by rw [proj_mul T h1 h2 l k (Finset.mem_filter.1 hk).2]
    _ = proj T l := rfl

theorem proj_succ (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (k : Fin a) :
    proj T (k.val + 1) = proj T k.val + T k * (T k)ᴴ := by
  have hs : univ.filter (fun i : Fin a => i.val < k.val + 1)
      = insert k (univ.filter (fun i : Fin a => i.val < k.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold proj
  rw [hs, Finset.sum_insert (by simp), add_comm]

theorem Jm_allPos' (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  unfold Formalism.REAL.Jm allPos
  simp

theorem exists_compress {m : ℕ} (X : Matrix (Fin n) (Fin m) ℂ) (hX : Xᴴ * X = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * g = 1) (hc : g * (X * Xᴴ) = X * Xᴴ * g) :
    ∃ k : Formalism.REAL.UJ (allPos m), g * (X * Xᴴ) = X * uMat k * Xᴴ := by
  have hgX : g * X = X * (Xᴴ * g * X) := by
    calc g * X = g * (X * (Xᴴ * X)) := by rw [hX, Matrix.mul_one]
      _ = g * (X * Xᴴ) * X := by simp only [Matrix.mul_assoc]
      _ = X * Xᴴ * g * X := by rw [hc]
      _ = X * (Xᴴ * g * X) := by simp only [Matrix.mul_assoc]
  have hkk : (Xᴴ * g * X)ᴴ * (Xᴴ * g * X) = 1 := by
    calc (Xᴴ * g * X)ᴴ * (Xᴴ * g * X) = Xᴴ * gᴴ * (X * (Xᴴ * g * X)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Xᴴ * gᴴ * (g * X) := by rw [hgX]
      _ = Xᴴ * (gᴴ * g) * X := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Matrix.mul_one, hX]
  refine ⟨⟨⟨Xᴴ * g * X, (Xᴴ * g * X)ᴴ, mul_eq_one_comm.1 hkk, hkk⟩, ?_⟩, ?_⟩
  · show (Xᴴ * g * X)ᴴ * Formalism.REAL.Jm (allPos m) * (Xᴴ * g * X) = Formalism.REAL.Jm (allPos m)
    rw [Jm_allPos', Matrix.mul_one, hkk]
  · show g * (X * Xᴴ) = X * (Xᴴ * g * X) * Xᴴ
    rw [← hgX, Matrix.mul_assoc]

theorem block_mul {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h1 : ∀ i, (T i)ᴴ * T i = 1) (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0)
    (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) (h4 : ∀ i, (T i)ᴴ * P = 0) (h5 : ∀ i, (T i)ᴴ * Q = 0)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) (k : Fin a) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * T k
      = T k * c k := by
  have hP : Pᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h4 k)
  have hQ : Qᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h5 k)
  have h3' : ∀ i k, (T i)ᴴ * (J * T k) = 0 := fun i k => by rw [← Matrix.mul_assoc]; exact h3 i k
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.sum_mul, Finset.sum_eq_single k]
  · simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3', hP, hQ, Matrix.mul_zero, Matrix.mul_one,
      add_zero]
  · intro i _ hik
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2 i k hik, h3', Matrix.mul_zero, add_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

private theorem unit_lemma_5 {m : ℕ} (x : Formalism.REAL.UJ (allPos m)) : (uMat x)ᴴ * uMat x = 1 := by
  have h : (uMat x)ᴴ * Formalism.REAL.Jm (allPos m) * uMat x = Formalism.REAL.Jm (allPos m) := x.2
  rwa [Jm_allPos', Matrix.mul_one] at h

private theorem block_sum_mul_J_mul_T {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h1 : ∀ i, (T i)ᴴ * T i = 1) (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0)
    (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) (h4 : ∀ i, (T i)ᴴ * P = 0) (h5 : ∀ i, (T i)ᴴ * Q = 0)
    (hJJ : J * J = 1) (hPJ : Pᴴ * J = Pᴴ) (hQJ : Qᴴ * J = -Qᴴ)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) (k : Fin a) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * (J * T k) = J * T k * c k := by
  have hPT : Pᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h4 k)
  have hQT : Qᴴ * T k = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (h5 k)
  have hPJT : Pᴴ * (J * T k) = 0 := by rw [← Matrix.mul_assoc, hPJ, hPT]
  have hQJT : Qᴴ * (J * T k) = 0 := by rw [← Matrix.mul_assoc, hQJ, Matrix.neg_mul, hQT, neg_zero]
  have h3' : ∀ i k, (T i)ᴴ * (J * T k) = 0 := fun i k => by rw [← Matrix.mul_assoc]; exact h3 i k
  have hJJ' : ∀ {r : ℕ} (X : Matrix (Fin n) (Fin r) ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.sum_mul, Finset.sum_eq_single k]
  · simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3', hJJ', hPJT, hQJT, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero]
  · intro i _ hik
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2 i k hik, h3', hJJ', Matrix.mul_zero, add_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

private theorem block_sum_mul_P {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h4 : ∀ i, (T i)ᴴ * P = 0) (hJP : J * P = P) (hP1 : Pᴴ * P = 1) (hQP : Qᴴ * P = 0)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * P = P * u := by
  simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_assoc, hJP, h4, hP1, hQP, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem block_sum_mul_Q {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (h5 : ∀ i, (T i)ᴴ * Q = 0) (hJQ : J * Q = -Q) (hQ1 : Qᴴ * Q = 1) (hPQ : Pᴴ * Q = 0)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ) * Q = Q * v := by
  simp only [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_assoc, hJQ, Matrix.mul_neg, h5, hQ1, hPQ,
    neg_zero, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem conjTranspose_block_sum_eq {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (hJH : Jᴴ = J) (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (u : Matrix (Fin p') (Fin p') ℂ)
    (v : Matrix (Fin q') (Fin q') ℂ) :
    ((∑ i, (T i * c i * (T i)ᴴ + J * T i * c i * (T i)ᴴ * J)) + P * u * Pᴴ + Q * v * Qᴴ)ᴴ = ((∑ i, (T i * (c i)ᴴ * (T i)ᴴ + J * T i * (c i)ᴴ * (T i)ᴴ * J)) + P * uᴴ * Pᴴ + Q * vᴴ * Qᴴ) := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJH, Matrix.mul_assoc]

private theorem ext_of_frame_eq {p' q' : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ)
    (hc : (∑ i, (T i * (T i)ᴴ + J * T i * (T i)ᴴ * J)) + P * Pᴴ + Q * Qᴴ = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i, A * T i = B * T i) (hJT : ∀ i, A * J * T i = B * J * T i)
    (hP : A * P = B * P) (hQ : A * Q = B * Q) : A = B := by
  calc A = A * ((∑ i, (T i * (T i)ᴴ + J * T i * (T i)ᴴ * J)) + P * Pᴴ + Q * Qᴴ) := by
        rw [hc, Matrix.mul_one]
    _ = B * ((∑ i, (T i * (T i)ᴴ + J * T i * (T i)ᴴ * J)) + P * Pᴴ + Q * Qᴴ) := by
        simp only [Matrix.mul_add, Matrix.mul_sum, ← Matrix.mul_assoc, hT, hJT, hP, hQ]
    _ = B := by rw [hc, Matrix.mul_one]

private theorem proj_mulVec_mulVec_eq_of_invariant (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (hA : ∀ i, A * T i = T i * c i) (y : Fin n → ℂ)
    (hy : proj T l *ᵥ y = y) : proj T l *ᵥ (A *ᵥ y) = A *ᵥ y := by
  have e : proj T l *ᵥ (A *ᵥ (proj T l *ᵥ y)) = A *ᵥ (proj T l *ᵥ y) := by
    simp only [Matrix.mulVec_mulVec]
    rw [proj_keep T h1 h2 l A c hA]
  rwa [hy] at e

private theorem inv_of_eq_mul_inv_mul (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (l : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ y, proj T l *ᵥ y = y → proj T l *ᵥ (A *ᵥ y) = A *ᵥ y)
    (hA' : ∀ y, proj T l *ᵥ y = y → proj T l *ᵥ (Aᴴ *ᵥ y) = Aᴴ *ᵥ y) :
    A * proj T l = proj T l * A := by
  have key : ∀ B : Matrix (Fin n) (Fin n) ℂ,
      (∀ y, proj T l *ᵥ y = y → proj T l *ᵥ (B *ᵥ y) = B *ᵥ y) →
        proj T l * (B * proj T l) = B * proj T l := by
    intro B hB
    refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    simp only [Matrix.toLin'_apply]
    have hz : proj T l *ᵥ (proj T l *ᵥ y) = proj T l *ᵥ y := by
      rw [Matrix.mulVec_mulVec, proj_idem T h1 h2 l]
    simp only [← Matrix.mulVec_mulVec]
    exact hB _ hz
  have e1 := key A hA
  have e2 := key Aᴴ hA'
  have e3 : proj T l * A * proj T l = proj T l * A := by
    have h := congrArg Matrix.conjTranspose e2
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, proj_conjTranspose,
      Matrix.mul_assoc] using h
  calc A * proj T l = proj T l * (A * proj T l) := e1.symm
    _ = proj T l * A := by rw [← Matrix.mul_assoc, e3]

theorem mem_maxK_inter_flagM_iff : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (p' q' : ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ), ((∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) ∧ (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y) → ∀ g : Formalism.REAL.UJ ε, g ∈ maxK ε ∩ flagM ε W ↔ ∃ (k : ∀ i, Formalism.REAL.UJ (allPos (j i))) (u : Formalism.REAL.UJ (allPos p')) (v : Formalism.REAL.UJ (allPos q')), uMat g = (∑ i, (T i * uMat (k i) * (T i)ᴴ + Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * uMat u * Pᴴ + Q * uMat v * Qᴴ := by
  rintro n ε a j W p' q' T P Q ⟨h1, h2, h3, h4, h5, hP1, hQ1, hJP, hJQ, hc, hW⟩ g
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJH : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hPJ : Pᴴ * Formalism.REAL.Jm ε = Pᴴ := by
    simpa [Matrix.conjTranspose_mul, hJH] using congrArg Matrix.conjTranspose hJP
  have hQJ : Qᴴ * Formalism.REAL.Jm ε = -Qᴴ := by
    simpa [Matrix.conjTranspose_mul, hJH] using congrArg Matrix.conjTranspose hJQ
  have hQP : Qᴴ * P = 0 := by
    have e : Qᴴ * P = -(Qᴴ * P) := by
      calc Qᴴ * P = Qᴴ * (Formalism.REAL.Jm ε * P) := by rw [hJP]
        _ = Qᴴ * Formalism.REAL.Jm ε * P := (Matrix.mul_assoc _ _ _).symm
        _ = -(Qᴴ * P) := by rw [hQJ, Matrix.neg_mul]
    ext x y
    have e' := congrFun (congrFun e x) y
    rw [Matrix.neg_apply] at e'
    rw [Matrix.zero_apply]
    linear_combination e' / 2
  have hPQ : Pᴴ * Q = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hQP
  constructor
  · rintro ⟨hK, hM⟩
    have hK' : (uMat g)ᴴ * uMat g = 1 := hK
    have hM' : ∀ (l : Fin (a + 1)), ∀ y ∈ W l, uMat g *ᵥ y ∈ W l ∧ (uMat g)ᴴ *ᵥ y ∈ W l := hM
    have hUJ : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
    have hgg : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.1 hK'
    have hgJ : uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g := by
      calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hUJ]
        _ = uMat g * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * uMat g := by rw [hgg, Matrix.one_mul]
    have hcomm : ∀ l : Fin (a + 1), uMat g * proj T l.val = proj T l.val * uMat g := fun l =>
      inv_of_eq_mul_inv_mul T h1 h2 l.val (uMat g)
        (fun y hy => (hW l _).1 (hM' l y ((hW l y).2 hy)).1)
        (fun y hy => (hW l _).1 (hM' l y ((hW l y).2 hy)).2)
    have hTT : ∀ i : Fin a, uMat g * (T i * (T i)ᴴ) = T i * (T i)ᴴ * uMat g := by
      intro i
      have c1 := hcomm i.succ
      have c0 := hcomm i.castSucc
      rw [Fin.val_succ, proj_succ T i] at c1
      rw [Fin.val_castSucc] at c0
      have e : T i * (T i)ᴴ = (proj T i.val + T i * (T i)ᴴ) - proj T i.val := by abel
      rw [e, Matrix.mul_sub, Matrix.sub_mul, c1, c0]
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε) := ⟨_, rfl⟩
    rw [← hS] at hc
    have hgS : uMat g * S = S * uMat g := by
      rw [hS, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_add, Matrix.add_mul, hTT i]
      congr 1
      calc uMat g * (Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε) = uMat g * Formalism.REAL.Jm ε * (T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * (uMat g * (T i * (T i)ᴴ)) * Formalism.REAL.Jm ε := by rw [hgJ]; simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * (T i * (T i)ᴴ * uMat g) * Formalism.REAL.Jm ε := by rw [hTT i]
        _ = Formalism.REAL.Jm ε * T i * (T i)ᴴ * (uMat g * Formalism.REAL.Jm ε) := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε * uMat g := by rw [hgJ]; simp only [Matrix.mul_assoc]
    have hR : P * Pᴴ + Q * Qᴴ = 1 - S := by rw [← hc]; abel
    have hgR : uMat g * (P * Pᴴ + Q * Qᴴ) = (P * Pᴴ + Q * Qᴴ) * uMat g := by
      rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hgS]
    have hRJ : (P * Pᴴ + Q * Qᴴ) * Formalism.REAL.Jm ε = P * Pᴴ - Q * Qᴴ := by
      simp only [Matrix.add_mul, Matrix.mul_assoc, hPJ, hQJ, Matrix.mul_neg, sub_eq_add_neg]
    have hgPP : uMat g * (P * Pᴴ) = P * Pᴴ * uMat g := by
      have e1 : ∀ R : Matrix (Fin n) (Fin n) ℂ, uMat g * R = R * uMat g →
          uMat g * (R + R * Formalism.REAL.Jm ε) = (R + R * Formalism.REAL.Jm ε) * uMat g := by
        intro R hR'
        calc uMat g * (R + R * Formalism.REAL.Jm ε) = uMat g * R + uMat g * R * Formalism.REAL.Jm ε := by
              rw [Matrix.mul_add, Matrix.mul_assoc]
          _ = R * uMat g + R * (uMat g * Formalism.REAL.Jm ε) := by rw [hR', Matrix.mul_assoc]
          _ = (R + R * Formalism.REAL.Jm ε) * uMat g := by rw [hgJ, Matrix.add_mul, Matrix.mul_assoc]
      have e2 := e1 _ hgR
      rw [hRJ] at e2
      have hsum : P * Pᴴ + Q * Qᴴ + (P * Pᴴ - Q * Qᴴ) = P * Pᴴ + P * Pᴴ := by abel
      have e3 : uMat g * (P * Pᴴ) + uMat g * (P * Pᴴ) = P * Pᴴ * uMat g + P * Pᴴ * uMat g := by
        rw [hsum, Matrix.mul_add, Matrix.add_mul] at e2
        exact e2
      ext x y
      have e4 := congrFun (congrFun e3 x) y
      simp only [Matrix.add_apply] at e4
      linear_combination e4 / 2
    have hgQQ : uMat g * (Q * Qᴴ) = Q * Qᴴ * uMat g := by
      have e : Q * Qᴴ = (P * Pᴴ + Q * Qᴴ) - P * Pᴴ := by abel
      rw [e, Matrix.mul_sub, Matrix.sub_mul, hgR, hgPP]
    choose k hk using fun i => exists_compress (T i) (h1 i) (uMat g) hK' (hTT i)
    obtain ⟨u, hu⟩ := exists_compress P hP1 (uMat g) hK' hgPP
    obtain ⟨v, hv⟩ := exists_compress Q hQ1 (uMat g) hK' hgQQ
    refine ⟨k, u, v, ?_⟩
    calc uMat g = uMat g * (S + P * Pᴴ + Q * Qᴴ) := by rw [hc, Matrix.mul_one]
      _ = uMat g * S + uMat g * (P * Pᴴ) + uMat g * (Q * Qᴴ) := by
          rw [Matrix.mul_add, Matrix.mul_add]
      _ = (∑ i, (T i * uMat (k i) * (T i)ᴴ + Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε))
            + P * uMat u * Pᴴ + Q * uMat v * Qᴴ := by
          rw [hu, hv, hS, Matrix.mul_sum]
          congr 2
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_add, hk i]
          congr 1
          calc uMat g * (Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε) = uMat g * Formalism.REAL.Jm ε * (T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
                simp only [Matrix.mul_assoc]
            _ = Formalism.REAL.Jm ε * (uMat g * (T i * (T i)ᴴ)) * Formalism.REAL.Jm ε := by rw [hgJ]; simp only [Matrix.mul_assoc]
            _ = Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε := by rw [hk i]; simp only [Matrix.mul_assoc]
  · rintro ⟨k, u, v, hg⟩
    have hA : ∀ i, uMat g * T i = T i * uMat (k i) := fun i => by
      rw [hg]; exact block_mul _ T P Q h1 h2 h3 h4 h5 _ _ _ i
    have hgH : (uMat g)ᴴ = (∑ i, (T i * (uMat (k i))ᴴ * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (uMat (k i))ᴴ * (T i)ᴴ * Formalism.REAL.Jm ε))
        + P * (uMat u)ᴴ * Pᴴ + Q * (uMat v)ᴴ * Qᴴ := by
      rw [hg]; exact conjTranspose_block_sum_eq _ T P Q hJH _ _ _
    have hAH : ∀ i, (uMat g)ᴴ * T i = T i * (uMat (k i))ᴴ := fun i => by
      rw [hgH]; exact block_mul _ T P Q h1 h2 h3 h4 h5 _ _ _ i
    refine Set.mem_inter ?_ ?_
    · show (uMat g)ᴴ * uMat g = 1
      have hJA : ∀ i, uMat g * (Formalism.REAL.Jm ε * T i) = Formalism.REAL.Jm ε * T i * uMat (k i) := fun i => by
        rw [hg]; exact block_sum_mul_J_mul_T _ T P Q h1 h2 h3 h4 h5 hJJ hPJ hQJ _ _ _ i
      have hJAH : ∀ i, (uMat g)ᴴ * (Formalism.REAL.Jm ε * T i) = Formalism.REAL.Jm ε * T i * (uMat (k i))ᴴ := fun i => by
        rw [hgH]; exact block_sum_mul_J_mul_T _ T P Q h1 h2 h3 h4 h5 hJJ hPJ hQJ _ _ _ i
      have hPA : uMat g * P = P * uMat u := by
        rw [hg]; exact block_sum_mul_P _ T P Q h4 hJP hP1 hQP _ _ _
      have hPAH : (uMat g)ᴴ * P = P * (uMat u)ᴴ := by
        rw [hgH]; exact block_sum_mul_P _ T P Q h4 hJP hP1 hQP _ _ _
      have hQA : uMat g * Q = Q * uMat v := by
        rw [hg]; exact block_sum_mul_Q _ T P Q h5 hJQ hQ1 hPQ _ _ _
      have hQAH : (uMat g)ᴴ * Q = Q * (uMat v)ᴴ := by
        rw [hgH]; exact block_sum_mul_Q _ T P Q h5 hJQ hQ1 hPQ _ _ _
      refine ext_of_frame_eq _ T P Q hc _ _ ?_ ?_ ?_ ?_
      · intro i
        simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hA i, ← Matrix.mul_assoc, hAH i, Matrix.mul_assoc (T i), unit_lemma_5, Matrix.mul_one]
      · intro i
        simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hJA i, ← Matrix.mul_assoc, hJAH i, Matrix.mul_assoc (Formalism.REAL.Jm ε * T i), unit_lemma_5, Matrix.mul_one]
      · simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hPA, ← Matrix.mul_assoc, hPAH, Matrix.mul_assoc P, unit_lemma_5, Matrix.mul_one]
      · simp only [Matrix.mul_assoc, Matrix.one_mul]
        rw [hQA, ← Matrix.mul_assoc, hQAH, Matrix.mul_assoc Q, unit_lemma_5, Matrix.mul_one]
    · show ∀ (l : Fin (a + 1)), ∀ y ∈ W l, uMat g *ᵥ y ∈ W l ∧ (uMat g)ᴴ *ᵥ y ∈ W l
      intro l y hy
      have hy' : proj T l.val *ᵥ y = y := (hW l y).1 hy
      exact ⟨(hW l _).2 (proj_mulVec_mulVec_eq_of_invariant T h1 h2 l.val _ _ hA y hy'),
        (hW l _).2 (proj_mulVec_mulVec_eq_of_invariant T h1 h2 l.val _ _ hAH y hy')⟩

end GlobalTheory.FlagLeviRange
