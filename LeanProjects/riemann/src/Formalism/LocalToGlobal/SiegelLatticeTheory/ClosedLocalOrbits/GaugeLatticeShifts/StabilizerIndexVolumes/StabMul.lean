import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.StabShape

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

section MulL

variable {E K : Type*} [Field E] [CommRing K] {r : ℕ}

theorem lL_eq (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (a : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    lL ι cj Dd a = Matrix.diagonal (fun i => cj (Dd i)) * a.map ι *
      Matrix.diagonal (fun i => Ring.inverse (cj (Dd i))) := by
  ext i j
  simp [lL, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]

theorem lL_mul (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (hD : ∀ i, IsUnit (Dd i))
    (a a' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : lL ι cj Dd (a * a') = lL ι cj Dd a * lL ι cj Dd a' := by
  have hinv : Matrix.diagonal (fun i => Ring.inverse (cj (Dd i))) * Matrix.diagonal (fun i => cj (Dd i)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.inverse_mul_cancel _ ((hD i).map cj)
  rw [lL_eq, lL_eq, lL_eq, Matrix.map_mul]
  set Dc := Matrix.diagonal (fun i => cj (Dd i))
  set Di := Matrix.diagonal (fun i => Ring.inverse (cj (Dd i)))
  rw [show Dc * a.map ι * Di * (Dc * a'.map ι * Di) = Dc * a.map ι * (Di * Dc) * a'.map ι * Di by
    simp only [Matrix.mul_assoc], hinv, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

def sgnE (K : Type*) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun i => (-1) ^ (r - i.val)

theorem sgnE_sq (K : Type*) [CommRing K] (r : ℕ) : sgnE K r * sgnE K r = 1 := by
  rw [sgnE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem ρL_eq (ι : E →+* K) (Dd : Fin (r + 1) → K) (b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ρL ι Dd b = Matrix.diagonal (fun i => Ring.inverse (Dd i)) * (sgnE E r * b * sgnE E r).map ι *
      Matrix.diagonal Dd := by
  ext i j
  simp [ρL, sgnE, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc, mul_comm, mul_left_comm]

theorem ρL_mul (ι : E →+* K) (Dd : Fin (r + 1) → K) (hD : ∀ i, IsUnit (Dd i))
    (b b' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ρL ι Dd (b' * b) = ρL ι Dd b' * ρL ι Dd b := by
  have hinv : Matrix.diagonal Dd * Matrix.diagonal (fun i => Ring.inverse (Dd i)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.mul_inverse_cancel _ (hD i)
  have hS : sgnE E r * (b' * b) * sgnE E r = (sgnE E r * b' * sgnE E r) * (sgnE E r * b * sgnE E r) := by
    calc sgnE E r * (b' * b) * sgnE E r = sgnE E r * b' * (sgnE E r * sgnE E r) * b * sgnE E r := by
          rw [sgnE_sq]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  rw [ρL_eq, ρL_eq, ρL_eq, hS, Matrix.map_mul]
  set Dm := Matrix.diagonal Dd
  set Di := Matrix.diagonal (fun i => Ring.inverse (Dd i))
  set B1 := (sgnE E r * b' * sgnE E r).map ι
  set B2 := (sgnE E r * b * sgnE E r).map ι
  rw [show Di * B1 * Dm * (Di * B2 * Dm) = Di * B1 * (Dm * Di) * B2 * Dm by simp only [Matrix.mul_assoc], hinv,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end MulL

section MulG

open Matrix

variable {E F K : Type*} [Field E] [Field F] [CommRing K] [Algebra F K] {r : ℕ}

theorem cx_lG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cx e (lG e ι Dd a b) = Matrix.diagonal (fun i => (e (Dd i)).2) *
      a.map ((RingHom.fst F F).comp ((e : K →+* F × F).comp ι)) * Matrix.diagonal (fun i => ((e (Dd i)).2)⁻¹) := by
  ext i j
  simp only [cx, lG, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe,
    AlgEquiv.apply_symm_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv]

theorem cy_lG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cy e (lG e ι Dd a b) = Matrix.diagonal (fun i => (e (Dd i)).2) *
      ((sgnE E r * b * sgnE E r).map ((RingHom.snd F F).comp ((e : K →+* F × F).comp ι)))ᵀ *
        Matrix.diagonal (fun i => ((e (Dd i)).2)⁻¹) := by
  ext i j
  simp only [cy, lG, sgnE, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe,
    AlgEquiv.apply_symm_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv, Matrix.transpose_apply, map_mul,
    Prod.snd_mul]
  ring

theorem cx_ρG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cx e (ρG e ι Dd a b) = Matrix.diagonal (fun i => ((e (Dd i)).1)⁻¹) *
      (sgnE E r * b * sgnE E r).map ((RingHom.fst F F).comp ((e : K →+* F × F).comp ι)) *
        Matrix.diagonal (fun i => (e (Dd i)).1) := by
  ext i j
  simp [cx, ρG, sgnE, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv]
  ring

theorem cy_ρG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cy e (ρG e ι Dd a b) = Matrix.diagonal (fun i => ((e (Dd i)).1)⁻¹) *
      (a.map ((RingHom.snd F F).comp ((e : K →+* F × F).comp ι)))ᵀ * Matrix.diagonal (fun i => (e (Dd i)).1) := by
  ext i j
  simp [cy, ρG, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv, Matrix.transpose_apply]
  ring

theorem diag_inv_mul {n : ℕ} (d : Fin n → F) (hd : ∀ i, d i ≠ 0) :
    Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hd i)

theorem diag_mul_inv {n : ℕ} (d : Fin n → F) (hd : ∀ i, d i ≠ 0) :
    Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i)

theorem sandwich {n : ℕ} (P Pi X Y : Matrix (Fin n) (Fin n) F) (h : Pi * P = 1) :
    P * X * Pi * (P * Y * Pi) = P * (X * Y) * Pi := by
  rw [show P * X * Pi * (P * Y * Pi) = P * X * (Pi * P) * Y * Pi by simp only [Matrix.mul_assoc], h, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem sgn_mul (b' b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    sgnE E r * (b' * b) * sgnE E r = (sgnE E r * b' * sgnE E r) * (sgnE E r * b * sgnE E r) := by
  rw [show (sgnE E r * b' * sgnE E r) * (sgnE E r * b * sgnE E r) = sgnE E r * b' * (sgnE E r * sgnE E r) * b * sgnE E r by
    simp only [Matrix.mul_assoc], sgnE_sq, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem lG_mul (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (hx : ∀ i, (e (Dd i)).1 ≠ 0)
    (hy : ∀ i, (e (Dd i)).2 ≠ 0) (a b a' b' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    lG e ι Dd (a * a') (b' * b) = lG e ι Dd a b * lG e ι Dd a' b' := by
  apply eq_of_cxy e
  · rw [cx_mul, cx_lG, cx_lG, cx_lG, Matrix.map_mul, sandwich _ _ _ _ (diag_inv_mul _ hy)]
  · rw [cy_mul, cy_lG, cy_lG, cy_lG, sgn_mul, Matrix.map_mul, Matrix.transpose_mul,
      sandwich _ _ _ _ (diag_inv_mul _ hy)]

theorem ρG_mul (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (hx : ∀ i, (e (Dd i)).1 ≠ 0)
    (hy : ∀ i, (e (Dd i)).2 ≠ 0) (a b a' b' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ρG e ι Dd (a * a') (b' * b) = ρG e ι Dd a' b' * ρG e ι Dd a b := by
  apply eq_of_cxy e
  · rw [cx_mul, cx_ρG, cx_ρG, cx_ρG, sgn_mul, Matrix.map_mul, sandwich _ _ _ _ (diag_mul_inv _ hx)]
  · rw [cy_mul, cy_ρG, cy_ρG, cy_ρG, Matrix.map_mul, Matrix.transpose_mul,
      sandwich _ _ _ _ (diag_mul_inv _ hx)]

end MulG

section RecMul

open Formalism.L2.SG.PairVal Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem lOf_mul {p : PlF D} (hA : Agree δ M p) (a b a' b' : MatR D) :
    lOf δ M p (a * a') (b' * b) = lOf δ M p a b * lOf δ M p a' b' := by
  cases h : (M p).split with
  | none => simp only [lOf, h]; exact lL_mul _ _ _ (frFac_unit δ M hA) a a'
  | some g =>
    simp only [lOf, h]
    exact lG_mul g.e _ _ (fun i => (split_units δ M hA g i).1) (fun i => (split_units δ M hA g i).2) a b a' b'

theorem ρOf_mul {p : PlF D} (hA : Agree δ M p) (a b a' b' : MatR D) :
    ρOf δ M p (a * a') (b' * b) = ρOf δ M p a' b' * ρOf δ M p a b := by
  cases h : (M p).split with
  | none => simp only [ρOf, h]; exact ρL_mul _ _ (frFac_unit δ M hA) b b'
  | some g =>
    simp only [ρOf, h]
    exact ρG_mul g.e _ _ (fun i => (split_units δ M hA g i).1) (fun i => (split_units δ M hA g i).2) a b a' b'

theorem cx_one {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F) :
    cx e (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cy_one {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F) :
    cy e (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem lOf_one {p : PlF D} (hA : Agree δ M p) : lOf δ M p 1 1 = 1 := by
  cases h : (M p).split with
  | none =>
    simp only [lOf, h]
    rw [lL_eq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _)
  | some g =>
    simp only [lOf, h]
    have hy := fun i => (split_units δ M hA g i).2
    apply eq_of_cxy g.e
    · rw [cx_lG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, diag_mul_inv _ hy, cx_one]
    · rw [cy_lG, Matrix.mul_one, sgnE_sq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one,
        Matrix.mul_one, diag_mul_inv _ hy, cy_one]

theorem ρOf_one {p : PlF D} (hA : Agree δ M p) : ρOf δ M p 1 1 = 1 := by
  cases h : (M p).split with
  | none =>
    simp only [ρOf, h]
    rw [ρL_eq, Matrix.mul_one, sgnE_sq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact Ring.inverse_mul_cancel _ (frFac_unit δ M hA i)
  | some g =>
    simp only [ρOf, h]
    have hx := fun i => (split_units δ M hA g i).1
    apply eq_of_cxy g.e
    · rw [cx_ρG, Matrix.mul_one, sgnE_sq, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        diag_inv_mul _ hx, cx_one]
    · rw [cy_ρG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
        diag_inv_mul _ hx, cy_one]

end RecMul

end Formalism.L2.SG.Pf.StabShape
