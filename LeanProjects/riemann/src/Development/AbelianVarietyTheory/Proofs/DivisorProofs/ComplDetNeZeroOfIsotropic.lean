import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW

set_option autoImplicit false

namespace GlobalTheory.ConstLat

theorem compl_map_ringHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {g : ℕ}
    (U : Matrix (Fin (g + g)) (Fin g) R) (L : Matrix (Fin g) (Fin (g + g)) R)
    (Ji : Matrix (Fin (g + g)) (Fin (g + g)) R) :
    (GlobalTheory.ConstLat.compl U L Ji).map f = GlobalTheory.ConstLat.compl (U.map f) (L.map f) (Ji.map f) := by
  ext i k
  refine Fin.addCases (fun l => ?_) (fun l => ?_) k
  · simp [GlobalTheory.ConstLat.compl]
  · simp only [GlobalTheory.ConstLat.compl, Matrix.map_apply, Matrix.of_apply, Fin.addCases_right]
    simp [Matrix.mul_apply, map_sum]

theorem compl_mulVec_eq {R : Type} [CommRing R] {g : ℕ}
    (U : Matrix (Fin (g + g)) (Fin g) R) (L : Matrix (Fin g) (Fin (g + g)) R)
    (Ji : Matrix (Fin (g + g)) (Fin (g + g)) R) (x : Fin (g + g) → R) :
    (GlobalTheory.ConstLat.compl U L Ji).mulVec x = U.mulVec (fun l => x (Fin.castAdd g l)) +
      (Ji * L.transpose).mulVec (fun l => x (Fin.natAdd g l.rev)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, GlobalTheory.ConstLat.compl, Matrix.of_apply, Fin.addCases_left,
    Fin.addCases_right, Pi.add_apply]
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm]
  simp

theorem compl_det_ne_zero_of_isotropic {K : Type} [Field K] {g : ℕ}
    (U : Matrix (Fin (g + g)) (Fin g) K) (L : Matrix (Fin g) (Fin (g + g)) K)
    (J Ji : Matrix (Fin (g + g)) (Fin (g + g)) K) (hL : L * U = 1) (hJ : J * Ji = 1)
    (h0 : U.transpose * J * U = 0) : (GlobalTheory.ConstLat.compl U L Ji).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [compl_mulVec_eq] at hx
  have h1 : U.transpose * J * (Ji * L.transpose) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJ, Matrix.one_mul, ← Matrix.transpose_mul, hL,
      Matrix.transpose_one]
  have h2 : (fun l : Fin g => x (Fin.natAdd g l.rev)) = 0 := by
    have := congrArg (U.transpose * J).mulVec hx
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h0, h1] at this
    simpa using this
  have h3 : (fun l : Fin g => x (Fin.castAdd g l)) = 0 := by
    rw [h2, Matrix.mulVec_zero, add_zero] at hx
    have := congrArg L.mulVec hx
    rw [Matrix.mulVec_mulVec, hL] at this
    simpa using this
  apply hx0
  funext k
  refine Fin.addCases (fun l => ?_) (fun l => ?_) k
  · exact congrFun h3 l
  · simpa using congrFun h2 l.rev

theorem isUnit_det_compl {R : Type} [CommRing R] [IsLocalRing R] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) R)
    (L : Matrix (Fin g) (Fin (g + g)) R) (J Ji : Matrix (Fin (g + g)) (Fin (g + g)) R) (hL : L * U = 1)
    (hJ : J * Ji = 1) (h0 : ∀ i j, ¬ IsUnit ((U.transpose * J * U) i j)) :
    IsUnit (GlobalTheory.ConstLat.compl U L Ji).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, compl_map_ringHom]
  refine compl_det_ne_zero_of_isotropic _ _ (J.map (IsLocalRing.residue R)) _ ?_ ?_ ?_
  · rw [← Matrix.map_mul, hL]; simp
  · rw [← Matrix.map_mul, hJ]; simp
  · rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have := h0 i j
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, not_not] at this
    simpa using this

end GlobalTheory.ConstLat
