import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.RealSymplForm

section Mat

open scoped ComplexOrder MatrixOrder

variable {k m n : ℕ}

theorem cartan_swap {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  calc sᴴ * G = sᴴ * G * (s * s) := by rw [h.1, Matrix.mul_one]
    _ = G * s := by rw [← Matrix.mul_assoc, h.2.1]

theorem cartan_herm {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : Gᴴ = G := by
  have h1 : (G * s)ᴴ = G * s := h.2.2.1
  have h2 : sᴴ * sᴴ = 1 := by rw [← conjTranspose_mul, h.1, conjTranspose_one]
  rw [conjTranspose_mul, ← cartan_swap h] at h1
  calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = G := by rw [h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem cartanInvolution_inv_eq_self {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : s⁻¹ = s :=
  Matrix.inv_eq_left_inv h.1

theorem cartan_inv_mul {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : (G * s)⁻¹ = s * G⁻¹ := by
  rw [Matrix.mul_inv_rev, cartanInvolution_inv_eq_self h]

theorem cartan_inv_conj {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : s * G⁻¹ * sᴴ = G⁻¹ := by
  conv_rhs => rw [← h.2.1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, cartanInvolution_inv_eq_self h, Matrix.mul_assoc]

theorem trace_pos {P : Matrix (Fin n) (Fin n) ℂ} {Q : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    {x : Matrix (Fin m) (Fin n) ℂ} (hx : x ≠ 0) : 0 < (P * xᴴ * Q * x).trace.re := by
  obtain ⟨B, hB, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hP.isStrictlyPositive
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hQ.isStrictlyPositive
  have e : (star B * B * xᴴ * (star C * C) * x).trace = ((C * x * Bᴴ)ᴴ * (C * x * Bᴴ)).trace := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hy : C * x * Bᴴ ≠ 0 := by
    intro h0
    apply hx
    have hB' : IsUnit (Bᴴ).det := (Matrix.isUnit_iff_isUnit_det _).1 hB.star
    have hC' : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).1 hC
    calc x = C⁻¹ * (C * x * Bᴴ) * (Bᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hB',
            Matrix.nonsing_inv_mul_cancel_left _ _ hC']
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  rw [e]
  have h1 := (posSemidef_conjTranspose_mul_self (C * x * Bᴴ)).trace_nonneg
  have h2 : ((C * x * Bᴴ)ᴴ * (C * x * Bᴴ)).trace ≠ 0 := fun h0 =>
    hy (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0)
  exact (Complex.pos_iff.1 (lt_of_le_of_ne h1 h2.symm)).1

theorem cplxO_cplxO {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s * s = 1) (ht : t * t = 1)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (cplxO s t x) = -x := by
  have e : t * (t * x * s) * s = x := by
    calc _ = (t * t) * x * (s * s) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hs, ht, Matrix.one_mul, Matrix.mul_one]
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, e, Complex.I_mul_I, neg_smul, one_smul]

theorem tr_conj {G : Matrix (Fin n) (Fin n) ℂ} {H : Matrix (Fin m) (Fin m) ℂ} (hG : Gᴴ = G) (hH : Hᴴ = H)
    (x y : Matrix (Fin m) (Fin n) ℂ) : (G⁻¹ * xᴴ * H * y).trace = star (G⁻¹ * yᴴ * H * x).trace := by
  rw [← Matrix.trace_conjTranspose]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG, hH, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem tr_J_left {G s : Matrix (Fin n) (Fin n) ℂ} {H t : Matrix (Fin m) (Fin m) ℂ} (hG : IsCartanInv G s)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * yᴴ * H * cplxO s t x).trace = Complex.I * ((G * s)⁻¹ * yᴴ * (H * t) * x).trace := by
  rw [cplxO, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, cartan_inv_mul hG, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem tr_J_J {G s : Matrix (Fin n) (Fin n) ℂ} {H t : Matrix (Fin m) (Fin m) ℂ} (hG : IsCartanInv G s)
    (hH : IsCartanInv H t) (x y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * (cplxO s t y)ᴴ * H * cplxO s t x).trace = (G⁻¹ * yᴴ * H * x).trace := by
  have e : (G * s)⁻¹ * (t * y * s)ᴴ * (H * t) * x = G⁻¹ * yᴴ * H * x := by
    calc _ = (s * G⁻¹ * sᴴ) * yᴴ * (tᴴ * H * t) * x := by
          simp only [cartan_inv_mul hG, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [cartan_inv_conj hG, hH.2.1]
  rw [tr_J_left hG, cplxO, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, e,
    smul_eq_mul, ← mul_assoc]
  simp

end Mat

theorem realPlace_imaginaryGenerator_re_eq_zero (D : D7) (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, tauE_sqrtMinusD, Complex.div_re]
  simp

theorem omAt_zero_right {D : D7} (S T : HSp D) (τ : D.what₂.Tau) (x : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {y : Matrix (Fin T.rank) (Fin S.rank) ℂ} (h : y = 0) : omAt S T τ x y = 0 := by
  simp [omAt, hAt, h]

open scoped ComplexOrder in
theorem omAt_J_neg {D : D7} (S T : HSp D) (τ : D.what₂.Tau) {s : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {t : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hs : IsCartanInv (gramAt D S τ) s) (ht : IsCartanInv (gramAt D T τ) t)
    {x : Matrix (Fin T.rank) (Fin S.rank) ℂ} (hx : x ≠ 0) : omAt S T τ (cplxO s t x) x < 0 := by
  have e : hAt S T τ (cplxO s t x) x = Complex.I *
      ((gramAt D S τ * s)⁻¹ * xᴴ * (gramAt D T τ * t) * x).trace := tr_J_left hs _ _
  have p := mul_pos (xi_zero_im_pos D τ) (trace_pos hs.2.2.inv ht.2.2 hx)
  simp only [omAt, e, Complex.mul_re, Complex.mul_im, realPlace_imaginaryGenerator_re_eq_zero, Complex.I_re, Complex.I_im]
  linarith

theorem form_alt_inv_def : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ x, jO S T sS sT (jO S T sS sT x) = -x) ∧ (∀ x y, omO S T x y = -omO S T y x) ∧ (∀ x y, omO S T (jO S T sS sT x) (jO S T sS sT y) = omO S T x y) ∧ ∀ x, x ≠ 0 → omO S T (jO S T sS sT x) x < 0 := by
  intro D S T sS sT hS hT
  refine ⟨fun x => ?_, fun x y => ?_, fun x y => ?_, fun x hx => ?_⟩
  · funext τ
    exact cplxO_cplxO (hS τ).1 (hT τ).1 _
  · rw [omO_apply, omO_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e : hAt S T τ (y τ) (x τ) = star (hAt S T τ (x τ) (y τ)) :=
      tr_conj (cartan_herm (hS τ)) (cartan_herm (hT τ)) _ _
    simp only [omAt, e, Complex.mul_re, realPlace_imaginaryGenerator_re_eq_zero, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  · rw [omO_apply, omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e : hAt S T τ (jO S T sS sT x τ) (jO S T sS sT y τ) = hAt S T τ (x τ) (y τ) :=
      tr_J_J (hS τ) (hT τ) _ _
    simp only [omAt, e]
  · obtain ⟨τ₀, h0⟩ := Function.ne_iff.1 hx
    rw [omO_apply]
    refine Finset.sum_neg' (fun τ _ => ?_) ⟨τ₀, Finset.mem_univ _, omAt_J_neg S T τ₀ (hS τ₀) (hT τ₀) h0⟩
    by_cases h : x τ = 0
    · exact (omAt_zero_right S T τ _ h).le
    · exact (omAt_J_neg S T τ (hS τ) (hT τ) h).le

end GlobalTheory.RealSymplForm
