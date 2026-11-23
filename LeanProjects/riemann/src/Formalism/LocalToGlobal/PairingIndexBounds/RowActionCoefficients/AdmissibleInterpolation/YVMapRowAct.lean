import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FinalTheorems

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

section Gen

variable {A A' : Type*} [CommRing A] [CommRing A']

theorem map_hvE (f : A →+* A') {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) : f (hvE x y c h hh) = hvE (fun a i => f (x a i)) (y.map f) c h hh := by
  unfold hvE
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i t
  simp [Matrix.map_apply, map_sum, map_mul]

theorem map_hvO (f : A →+* A') {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ) :
    f (hvO x y c h) = hvO (fun a i => f (x a i)) (y.map f) c h := by
  unfold hvO
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_catM]

theorem hvE_mul {n : ℕ} (g : Matrix (Fin n) (Fin n) A) (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) : hvE x (g * y) c h hh = hvE (mulC g.transpose x) y c h hh := by
  unfold hvE
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext i t
  simp only [Matrix.of_apply, Matrix.mul_apply, mulC, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hvO_mul {n : ℕ} (g : Matrix (Fin n) (Fin n) A) (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ) :
    hvO (mulC g x) (g * y) c h = g.det ^ c * hvO x y c h := by
  unfold hvO
  have : ∀ k : Fin c, (catM (h k) (g * y) (mulC g x)).det = g.det * (catM (h k) y x).det := by
    intro k
    rw [← mul_catM, Matrix.det_mul]
  rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Gen

section Row

variable {K : Type} [CommRing K] {n : ℕ}

theorem yV_map_rowAct (g : Matrix (Fin n) (Fin n) K) :
    (yV K n).map (rowAct K g) = g.map C * yV K n := by
  ext a t
  simp only [Matrix.map_apply, yV, Matrix.mul_apply]
  unfold rowAct
  rw [aeval_X]

theorem rowAct_hvE (g : Matrix (Fin n) (Fin n) K) (x : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ n) :
    rowAct K g (hvE (fun a i => C (x a i)) (yV K n) c h hh) = hvE (fun a i => C (mulC g.transpose x a i)) (yV K n) c h hh := by
  have h1 := map_hvE (rowAct K (n := n) g : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K)
    (fun a i => C (x a i)) (yV K n) c h hh
  rw [RingHom.coe_coe] at h1
  rw [h1, yV_map_rowAct g, hvE_mul]
  congr 1
  funext a i
  simp only [mulC, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact (rowAct K g).commutes _

theorem rowAct_hvO (g gi : Matrix (Fin n) (Fin n) K) (hg : g * gi = 1) (x : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) :
    rowAct K g (hvO (fun a i => C (x a i)) (yV K n) c h) = g.det ^ c • hvO (fun a i => C (mulC gi x a i)) (yV K n) c h := by
  have h1 := map_hvO (rowAct K (n := n) g : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K)
    (fun a i => C (x a i)) (yV K n) c h
  rw [RingHom.coe_coe] at h1
  rw [h1, yV_map_rowAct g]
  have h2 : (fun a i => rowAct K (n := n) g (C (x a i))) =
      mulC (g.map C) (fun a i => (C (mulC gi x a i) : MvPolynomial (Fin n × Fin n) K)) := by
    funext a i
    rw [show rowAct K (n := n) g (C (x a i)) = C (x a i) from (rowAct K g).commutes _]
    have h3 : x a i = mulC g (mulC gi x) a i := by rw [← mulC_mul, hg]; simp [mulC, Matrix.one_apply]
    rw [h3]
    simp only [mulC, Matrix.map_apply, map_sum, map_mul]
  rw [h2, hvO_mul, smul_eq_C_mul, map_pow]
  congr 2
  exact (RingHom.map_det C g).symm

end Row

end Formalism.L2.PairingIndexBounds.Ent
