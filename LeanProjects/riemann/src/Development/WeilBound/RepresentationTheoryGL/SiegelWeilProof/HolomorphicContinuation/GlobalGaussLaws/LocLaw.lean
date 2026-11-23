import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawE
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawC

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  exact this

theorem pqOf_add {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) :
    (pqOf ε l τ).1 + (pqOf ε l τ).2 = m := by
  unfold pqOf
  split_ifs
  · exact cnt_add ε
  · rw [add_comm]; exact cnt_add ε

theorem npow_sq (z : ℂ) (m : ℕ) : npow (‖z‖₊ ^ 2) ((m : ℂ) / 2) = ((‖z‖ : ℝ) : ℂ) ^ (m : ℤ) := by
  simp only [npow, NNReal.coe_pow, coe_nnnorm]
  rw [show ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (sq_nonneg _), ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg _),
    show ((2 : ℕ) : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast, zpow_natCast,
    Complex.ofReal_pow]

set_option maxHeartbeats 400000 in
theorem scal {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau} {m : ℕ} (k j : ℤ)
    (hk : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ k)
    (hj : k - m = j + j) (p q : ℕ) (hpq : p + q = m) (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    (χ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)))) ((m : ℂ) / 2) = F0 p q (k - j) y := by
  have hv : (unitAt hσ τ (aOf y hy)).1 = baseColumnsAt σ τ (mR y).toBlocks₁₁ := by rw [unitAt_val, aOf_val]
  have hxv : ((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)) : (AE D)ˣ) : AE D) =
      (baseColumnsAt σ τ (mR y).toBlocks₁₁).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hv]
  have hf : finPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, finite_part_adelic_point_matrix hσ, Matrix.det_one]
  have hcomp : ∀ τ', θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = (compAt θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁)).det := by
    intro τ'
    rw [hxv]
    show cf θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  have hτ : θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = ((mR y).toBlocks₁₁).det := by rw [hcomp, component_adelic_point_matrix hσ]
  have hne : ∀ τ', τ' ≠ τ → θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = 1 := fun τ' h => by
    rw [hcomp, component_adelic_point_ne hσ h, Matrix.det_one]
  have habs : absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖((mR y).toBlocks₁₁).det‖₊ ^ 2 := by
    rw [show absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D))‖₊ ^ 2 from GlobalTheory.StabAtPlace.absE_single hθ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) τ hf hne, hτ]
  rw [hk _ hf hne, hτ, habs, npow_sq]
  have hZ := det_ne y hy
  have hu1 : u1 (mR y) = (mR y).toBlocks₂₂ := by simp only [u1, hy, smul_zero, zero_add]
  have hu2 : u2 (mR y) = (mR y).toBlocks₂₂ := by simp only [u2, hy, smul_zero, neg_zero, zero_add]
  have hdy : (mR y).det = ((mR y).toBlocks₁₁).det * ((mR y).toBlocks₂₂).det := by
    conv_lhs => rw [fromBlocks_of y hy]
    rw [Matrix.det_fromBlocks_zero₂₁]
  have hR : ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hZ)
  have hd : ((mR y).toBlocks₂₂).det = ((mR y).toBlocks₁₁).det / ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
    have h1 : ((mR y).toBlocks₂₂).det = (star ((mR y).toBlocks₁₁).det)⁻¹ := eq_inv_of_mul_eq_one_right (det_rel y hy)
    have h2 : ((mR y).toBlocks₁₁).det * star ((mR y).toBlocks₁₁).det = ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have h3 : star ((mR y).toBlocks₁₁).det ≠ 0 := star_ne_zero.2 hZ
    rw [h1, eq_div_iff (pow_ne_zero 2 hR), ← h2]
    field_simp
  simp only [F0, f0, hu1, hu2, hdy, hd]
  exact alg_id _ _ hZ hR k j p q m hpq hj

end PositivityTheory.Rg.Sw.Glob.LocLawH

namespace PositivityTheory.Rg.Sw.Glob

theorem lIlaw : LIlaw := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  exact ⟨k - j, fun P y g hy => by
    rw [LocLawH.glob_law hC hL hσ P y g hy, LocLawH.scal hC.hθ hσ k j hk hj _ _ (LocLawH.pqOf_add ε l τ) y hy]⟩

end PositivityTheory.Rg.Sw.Glob
