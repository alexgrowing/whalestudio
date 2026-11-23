import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

noncomputable section

namespace GlobalTheory.CompanionTheory.MajC

theorem measurable_M22_apply (i j : Fin 2) : Measurable (fun h : M22 => h i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

theorem measurable_det_of_M22 : Measurable (fun h : M22 => (Matrix.of h).det) := by
  have h00 := measurable_M22_apply 0 0
  have h01 := measurable_M22_apply 0 1
  have h10 := measurable_M22_apply 1 0
  have h11 := measurable_M22_apply 1 1
  have : (fun h : M22 => (Matrix.of h).det) = fun h => h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    funext h
    simp [Matrix.det_fin_two]
  rw [this]
  exact (h00.mul h11).sub (h01.mul h10)

theorem eta_eq_inv_det (h : M22) (j : Fin 2) :
    eta h j = ((Matrix.of h).det)⁻¹ * (![-h 1 0, h 0 0] j) := by
  unfold eta
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
  fin_cases j <;> simp

theorem measurable_eta : Measurable eta := by
  refine measurable_pi_iff.2 fun j => ?_
  have : (fun h : M22 => eta h j) = fun h => ((Matrix.of h).det)⁻¹ * (![-h 1 0, h 0 0] j) := by
    funext h; exact eta_eq_inv_det h j
  rw [this]
  refine measurable_det_of_M22.inv.mul ?_
  fin_cases j
  · simpa using measurable_M22_apply 1 0
  · simpa using measurable_M22_apply 0 0

theorem measurable_jm_scaled (N : ℕ) (a b : ℂ) :
    Measurable (fun p : M22 × ℂ => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 a b) := by
  have hd : Measurable (fun p : M22 × ℂ => ‖(Matrix.of p.1).det‖) :=
    (measurable_det_of_M22.comp measurable_fst).norm
  have he : Measurable (fun p : M22 × ℂ => ‖eta p.1‖) :=
    (measurable_eta.comp measurable_fst).norm
  have hh : Measurable (fun p : M22 × ℂ => ‖p.1‖) := measurable_fst.norm
  have ht : Measurable (fun p : M22 × ℂ => ‖p.2‖) := measurable_snd.norm
  unfold jm
  have c1 : Measurable (fun _ : M22 × ℂ => (1 : ℝ)) := measurable_const
  have ca : Measurable (fun _ : M22 × ℂ => ‖a‖) := measurable_const
  have cb : Measurable (fun _ : M22 × ℂ => ‖b‖) := measurable_const
  refine ((hd.pow_const 2).inv).mul ?_
  refine Measurable.mul (Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_) ?_
  · exact (((hd.pow_const 2).mul (ht.pow_const 2)).mul (he.pow_const 2)).inv
  · exact ((c1.add hh).pow_const N).inv
  · exact ((c1.add (cb.mul he)).pow_const N).inv
  · exact ((ht.mul he).div (ca.add (ht.mul he))).pow_const N
  · exact ((c1.add (ht.div (hd.mul he))).pow_const N).inv

end GlobalTheory.CompanionTheory.MajC
