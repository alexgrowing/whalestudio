import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

namespace GlobalTheory.HenselSU

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_entries_right {J : Ideal R} (A B : Matrix n n R)
    (hB : ∀ a b, B a b ∈ J) : ∀ a b, (A * B) a b ∈ J := fun a b => by
  rw [Matrix.mul_apply]; exact J.sum_mem fun k _ => J.mul_mem_left _ (hB k b)

theorem mul_entries_left {J : Ideal R} (A B : Matrix n n R)
    (hA : ∀ a b, A a b ∈ J) : ∀ a b, (A * B) a b ∈ J := fun a b => by
  rw [Matrix.mul_apply]; exact J.sum_mem fun k _ => J.mul_mem_right _ (hA a k)

theorem mul_entries_mul {J K : Ideal R} (A B : Matrix n n R)
    (hA : ∀ a b, A a b ∈ J) (hB : ∀ a b, B a b ∈ K) : ∀ a b, (A * B) a b ∈ J * K := fun a b => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA a k) (hB k b)

theorem step_identity (w v : R) (hw : w + v = 1) (H : Matrix n n R) :
    (1 - v • H) * (H + 1) * (1 - w • H) - 1 = (v * w - 1) • (H * H) + (v * w) • (H * H * H) := by
  obtain rfl : v = 1 - w := by rw [← hw]; ring
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, Matrix.mul_assoc]
  module

theorem map_smul_ring (c : R →+* R) (w : R) (H : Matrix n n R) : (w • H).map c = c w • H.map c := by
  ext a b; simp

theorem herm_self (c : R →+* R) (hc : ∀ x, c (c x) = x) (A : Matrix n n R) :
    ((((A.map c)ᵀ * A - 1).map c))ᵀ = (A.map c)ᵀ * A - 1 := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, map_sum, hc, mul_comm, apply_ite c, eq_comm]

theorem step_herm (c : R →+* R) (hc : ∀ x, c (c x) = x) (w : R) (hw : w + c w = 1) (A : Matrix n n R) :
    ((A * (1 - w • ((A.map c)ᵀ * A - 1))).map c)ᵀ * (A * (1 - w • ((A.map c)ᵀ * A - 1))) - 1
      = (c w * w - 1) • (((A.map c)ᵀ * A - 1) * ((A.map c)ᵀ * A - 1))
        + (c w * w) • (((A.map c)ᵀ * A - 1) * ((A.map c)ᵀ * A - 1) * ((A.map c)ᵀ * A - 1)) := by
  set H := (A.map c)ᵀ * A - 1 with hH
  have h1 : ((A * (1 - w • H)).map c)ᵀ = (1 - c w • H) * (A.map c)ᵀ := by
    rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.map_sub (⇑c) (map_sub c), Matrix.map_one (⇑c) c.map_zero c.map_one,
      map_smul_ring, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, herm_self c hc A]
  have h2 : (A.map c)ᵀ * A = H + 1 := by rw [hH]; abel
  rw [h1, show (1 - c w • H) * (A.map c)ᵀ * (A * (1 - w • H)) = (1 - c w • H) * ((A.map c)ᵀ * A) * (1 - w • H) by
    simp only [Matrix.mul_assoc], h2]
  exact step_identity w (c w) hw H

theorem herm_cong (c : R →+* R) (J : Ideal R) (hJ : ∀ x ∈ J, c x ∈ J) (A B : Matrix n n R)
    (hAB : ∀ a b, A a b - B a b ∈ J) :
    ∀ a b, ((A.map c)ᵀ * A - 1) a b - ((B.map c)ᵀ * B - 1) a b ∈ J := by
  have hA : A = B + (A - B) := by abel
  have hE : ∀ a b, (A - B) a b ∈ J := fun a b => by simpa using hAB a b
  generalize A - B = E at hA hE
  subst hA
  have key : ((B + E).map c)ᵀ * (B + E) - 1 - ((B.map c)ᵀ * B - 1)
      = (B.map c)ᵀ * E + (E.map c)ᵀ * (B + E) := by
    rw [Matrix.map_add (⇑c) (map_add c), Matrix.transpose_add]; noncomm_ring
  have hEs : ∀ a b, (E.map c)ᵀ a b ∈ J := fun a b => by
    simp only [Matrix.transpose_apply, Matrix.map_apply]; exact hJ _ (hE b a)
  intro a b
  rw [← Matrix.sub_apply, key, Matrix.add_apply]
  exact J.add_mem (mul_entries_right _ _ hE a b) (mul_entries_left _ _ hEs a b)

theorem smul_top_pow (I : Ideal R) (k : ℕ) : (I ^ k • ⊤ : Submodule R R) = I ^ k := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem exists_unitary_limit (c : R →+* R) (hc : ∀ x, c (c x) = x) (I : Ideal R)
    (hI : ∀ x ∈ I, c x ∈ I) (hcomp : IsAdicComplete I R) (w : R) (hw : w + c w = 1)
    (g : Matrix n n R) (hg : ∀ a b, ((g.map c)ᵀ * g - 1) a b ∈ I) :
    ∃ L : Matrix n n R, (L.map c)ᵀ * L = 1 ∧ ∀ a b, L a b - g a b ∈ I := by
  set Hf : Matrix n n R → Matrix n n R := fun A => (A.map c)ᵀ * A - 1 with hHf
  set seq : ℕ → Matrix n n R := fun k => (fun A => A * (1 - w • Hf A))^[k] g with hseq
  have hseq_succ : ∀ k, seq (k + 1) = seq k * (1 - w • Hf (seq k)) := fun k => by
    simp only [hseq]; rw [Function.iterate_succ_apply']
  have hseq_zero : seq 0 = g := rfl
  have hH : ∀ k a b, Hf (seq k) a b ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro a b; rw [zero_add, pow_one, hseq_zero]; exact hg a b
    | succ k ih =>
      have e := step_herm c hc w hw (seq k)
      rw [← hseq_succ] at e
      have e' : Hf (seq (k + 1)) = (c w * w - 1) • (Hf (seq k) * Hf (seq k))
          + (c w * w) • (Hf (seq k) * Hf (seq k) * Hf (seq k)) := e
      have hHH : ∀ a b, (Hf (seq k) * Hf (seq k)) a b ∈ I ^ (k + 1 + 1) := fun a b =>
        Ideal.pow_le_pow_right (show k + 1 + 1 ≤ (k + 1) + (k + 1) by omega) (by rw [pow_add]; exact mul_entries_mul _ _ ih ih a b)
      intro a b
      rw [e', Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hHH a b))
        (Ideal.mul_mem_left _ _ (mul_entries_left _ _ hHH a b))
  have hdiff : ∀ k a b, seq (k + 1) a b - seq k a b ∈ I ^ (k + 1) := by
    intro k a b
    have : seq (k + 1) a b - seq k a b = -((seq k * (w • Hf (seq k))) a b) := by
      rw [hseq_succ, mul_sub, mul_one, Matrix.sub_apply]; ring
    rw [this]
    exact neg_mem (mul_entries_right _ _ (fun a b => by
      rw [Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hH k a b)) a b)
  have hcauchy : ∀ a b m k, m ≤ k → seq m a b - seq k a b ∈ I ^ m := by
    intro a b m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have : seq m a b - seq (k + 1) a b = (seq m a b - seq k a b) - (seq (k + 1) a b - seq k a b) := by ring
      rw [this]
      exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right (by omega) (hdiff k a b))
  have hlim : ∀ a b, ∃ x : R, ∀ k, seq k a b - x ∈ I ^ k := by
    intro a b
    obtain ⟨x, hx⟩ := hcomp.toIsPrecomplete.prec (f := fun k => seq k a b)
      (fun {m k} hmk => by rw [SModEq.sub_mem, smul_top_pow]; exact hcauchy a b m k hmk)
    exact ⟨x, fun k => by have := hx k; rwa [SModEq.sub_mem, smul_top_pow] at this⟩
  choose L hL using hlim
  have hIpow : ∀ k, ∀ x ∈ I ^ k, c x ∈ I ^ k := by
    intro k x hx
    have hle : Ideal.map c I ≤ I := Ideal.map_le_iff_le_comap.mpr fun y hy => hI y hy
    have h1 := Ideal.mem_map_of_mem c hx
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle k h1
  have hzero : ∀ a b, Hf (Matrix.of L) a b = 0 := by
    intro a b
    refine hcomp.toIsHausdorff.haus _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, smul_top_pow]
    have h1 := herm_cong c (I ^ k) (hIpow k) (Matrix.of L) (seq k) (fun a b => by
      rw [Matrix.of_apply, ← neg_sub]; exact neg_mem (hL a b k)) a b
    have h2 : Hf (seq k) a b ∈ I ^ k := Ideal.pow_le_pow_right (by omega) (hH k a b)
    have : Hf (Matrix.of L) a b = (Hf (Matrix.of L) a b - Hf (seq k) a b) + Hf (seq k) a b := by ring
    rw [this]; exact Ideal.add_mem _ h1 h2
  refine ⟨Matrix.of L, ?_, ?_⟩
  · have : Hf (Matrix.of L) = 0 := by ext a b; exact hzero a b
    exact sub_eq_zero.mp this
  · intro a b
    have h1 := hL a b 1
    have h2 := hdiff 0 a b
    rw [pow_one] at h1
    rw [zero_add, pow_one, hseq_zero] at h2
    have : Matrix.of L a b - g a b = -(seq 1 a b - L a b) + (seq (0 + 1) a b - g a b) := by
      rw [Matrix.of_apply]; ring
    rw [this]; exact Ideal.add_mem _ (neg_mem h1) h2

end GlobalTheory.HenselSU

namespace GlobalTheory.HenselSU

theorem hensel_special_unitary : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) →
    ∀ (I : Ideal R), (∀ x ∈ I, c x ∈ I) → IsAdicComplete I R → ∀ w : R, w + c w = 1 →
    ∀ (r : ℕ) (g : Matrix (Fin r) (Fin r) R), (∀ a b, ((g.map c)ᵀ * g - 1) a b ∈ I) →
    g.det - 1 ∈ I → ∃ g' : Matrix (Fin r) (Fin r) R,
      (g'.map c)ᵀ * g' = 1 ∧ g'.det = 1 ∧ ∀ a b, g' a b - g a b ∈ I := by
  intro R _ c hc I hI hcomp w hw r g hg hdet
  obtain ⟨L, hLu, hLg⟩ := exists_unitary_limit c hc I hI hcomp w hw g hg
  have hu : c L.det * L.det = 1 := by
    have := congrArg Matrix.det hLu
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det] at this
  have hu1 : L.det - 1 ∈ I := by
    have hmap : L.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I) := by
      ext a b; exact Ideal.Quotient.eq.mpr (hLg a b)
    have h1 : Ideal.Quotient.mk I L.det = Ideal.Quotient.mk I g.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have h2 := Ideal.Quotient.eq.mp h1
    have : L.det - 1 = (L.det - g.det) + (g.det - 1) := by ring
    rw [this]; exact I.add_mem h2 hdet
  rcases r with _ | r
  · exact ⟨1, by simp, by simp, fun a => a.elim0⟩
  · refine ⟨L * Matrix.diagonal (Function.update 1 0 (c L.det)), ?_, ?_, ?_⟩
    · rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (L.map c)ᵀ, hLu,
        Matrix.one_mul, Matrix.diagonal_map c.map_zero, Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      simp only [Function.update_apply]
      split_ifs
      · rw [hc, mul_comm, hu]
      · simp
    · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_succ]
      simp [Fin.succ_ne_zero]
      linear_combination hu
    · intro a b
      have hd1 : ∀ i, Function.update (1 : Fin (r + 1) → R) 0 (c L.det) i - 1 ∈ I := by
        intro i; simp only [Function.update_apply]; split_ifs
        · have := hI _ hu1; rwa [map_sub, map_one] at this
        · simp
      have : (L * Matrix.diagonal (Function.update (1 : Fin (r + 1) → R) 0 (c L.det)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) R) a b - g a b
          = L a b * (Function.update (1 : Fin (r + 1) → R) 0 (c L.det) b - 1) + (L a b - g a b) := by
        rw [Matrix.mul_diagonal]; ring
      rw [this]; exact I.add_mem (I.mul_mem_left _ (hd1 b)) (hLg a b)

end GlobalTheory.HenselSU
