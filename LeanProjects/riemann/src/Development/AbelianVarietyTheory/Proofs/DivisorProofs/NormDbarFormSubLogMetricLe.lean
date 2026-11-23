import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open Matrix Complex ComplexConjugate

namespace GlobalTheory.CurveDens

theorem proj_rank_two_identity (A Dr : ℝ) (C x y da q : ℂ) (hA : 0 < A) (hQpos : 0 < Dr - normSq C / A) :
    ‖(x * da + y * (A*q + da*((A:ℂ)⁻¹*C))) - (x * A + y * C) * (((A⁻¹:ℝ):ℂ) * da)‖^2 =
    (A * (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re - ‖x*A + y*C‖^2) *
      (Real.pi * (2 * (-I * (kappa * ((((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * conj (-q) * A * (-q)))).re)) := by
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have hX : (x * da + y * (A*q + da*((A:ℂ)⁻¹*C))) - (x * A + y * C) * (((A⁻¹:ℝ):ℂ) * da) = y * A * q := by
    have : (A:ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast; field_simp; ring
  have hT : (((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * conj (-q) * A * (-q) = ((A * normSq q / (Dr - normSq C / A) : ℝ) : ℂ) := by
    have h0 : conj (-q) * (-q) = (normSq q : ℂ) := by rw [map_neg, neg_mul_neg, mul_comm, Complex.mul_conj]
    have hQ0 : (Dr - normSq C / A) ≠ 0 := hQpos.ne'
    calc _ = (((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * A * (conj (-q) * (-q)) := by ring
      _ = _ := by rw [h0]; push_cast; field_simp
  rw [hX, hT, ← mul_assoc (-I) kappa, e, ← ofReal_mul, ofReal_re, Complex.sq_norm, Complex.sq_norm]
  have hF : (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re =
      A * normSq x + 2 * (x * conj C * conj y).re + Dr * normSq y := by
    simp [normSq_apply, mul_re, mul_im, conj_re, conj_im]; ring
  have hK : A * (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re - normSq (x*A + y*C) =
      A * normSq y * (Dr - normSq C / A) := by
    rw [hF]
    simp only [normSq_apply, mul_re, mul_im, conj_re, conj_im, add_re, add_im, ofReal_re, ofReal_im]
    field_simp
    ring
  rw [hK, normSq_mul, normSq_mul, normSq_ofReal]
  have hpi : 0 < Real.pi := Real.pi_pos
  generalize Dr - normSq C / A = Qr at hQpos ⊢
  field_simp

theorem norm_sq_dbar_proj_rank_two (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (G : E → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (s : E → Fin 1 ⊕ Fin 1 → ℂ) (ξ z : E) (hG : MContDiffAt 1 G z) (hP : ∀ᶠ x in 𝓝 z, (G x).PosDef) (hs : ∀ i, DifferentiableAt ℂ (fun x => s x i) z) : ‖dbar (fun x => form (G x) (s x) (Pi.single (Sum.inl 0) 1)) z ξ - form (G z) (s z) (Pi.single (Sum.inl 0) 1) * dbar (fun x => (Real.log (G x (Sum.inl 0) (Sum.inl 0)).re : ℂ)) z ξ‖ ^ 2 = ((G z (Sum.inl 0) (Sum.inl 0)).re * (form (G z) (s z) (s z)).re - ‖form (G z) (s z) (Pi.single (Sum.inl 0) 1)‖ ^ 2) * (Real.pi * (2 * diagVal (extTrace G z) ξ)) := by
  set i₁ : Fin 1 ⊕ Fin 1 := Sum.inl 0 with hi₁
  set i₂ : Fin 1 ⊕ Fin 1 := Sum.inr 0 with hi₂
  have hz : (G z).PosDef := hP.self_of_nhds
  have hform1 : ∀ x, form (G x) (s x) (Pi.single i₁ 1) = s x i₁ * G x i₁ i₁ + s x i₂ * G x i₂ i₁ :=
    fun x => by simp [i₁, i₂, form_eq_sum, Fintype.sum_sum_type, Pi.single_apply]
  have hformss : form (G z) (s z) (s z) = s z i₁ * G z i₁ i₁ * conj (s z i₁) + s z i₁ * G z i₁ i₂ * conj (s z i₂)
     + s z i₂ * G z i₂ i₁ * conj (s z i₁) + s z i₂ * G z i₂ i₂ * conj (s z i₂) := by
    simp [i₁, i₂, form_eq_sum, Fintype.sum_sum_type]; ring
  have hda : DifferentiableAt ℝ (fun x => G x i₁ i₁) z := (hG i₁ i₁).differentiableAt one_ne_zero
  have hdc : DifferentiableAt ℝ (fun x => G x i₂ i₁) z := (hG i₂ i₁).differentiableAt one_ne_zero
  have hsR : ∀ i, DifferentiableAt ℝ (fun x => s x i) z := fun i => (hs i).restrictScalars ℝ

  have h1 : dbar (fun x => form (G x) (s x) (Pi.single i₁ 1)) z ξ =
      s z i₁ * dbar (fun x => G x i₁ i₁) z ξ + s z i₂ * dbar (fun x => G x i₂ i₁) z ξ := by
    simp only [hform1]
    rw [dbar_add ((hsR i₁).fun_mul hda) ((hsR i₂).fun_mul hdc), ContinuousLinearMap.add_apply,
      dbar_mul (hsR i₁) hda, dbar_mul (hsR i₂) hdc, dbar_eq_zero (hs i₁), dbar_eq_zero (hs i₂)]
    simp

  have hreal : ∀ᶠ x in 𝓝 z, G x i₁ i₁ = ((G x i₁ i₁).re : ℂ) := hP.mono fun x hx => by
    have := (Complex.lt_def.1 (hx.diag_pos (i := i₁))).2
    exact Complex.ext (by simp) (by simp [← this])
  have hApos : 0 < (G z i₁ i₁).re := (Complex.lt_def.1 (hz.diag_pos (i := i₁))).1

  have h2 : dbar (fun x => (Real.log (G x i₁ i₁).re : ℂ)) z ξ =
      (((G z i₁ i₁).re)⁻¹ : ℝ) * dbar (fun x => G x i₁ i₁) z ξ := by
    have hg : DifferentiableAt ℝ (fun x => (G x i₁ i₁).re) z := (Complex.reCLM.differentiableAt).comp z hda
    rw [dbar_ofReal_comp (t := fun x => (G x i₁ i₁).re) (Real.hasDerivAt_log hApos.ne') hg,
      dbar_congr (hreal.mono fun x hx => hx.symm)]

  have hoc : ∀ x, orthCoeff (G x) 0 0 = (G x i₁ i₁)⁻¹ * G x i₂ i₁ := fun x => by
    simp [orthCoeff, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, i₁, i₂]
    rfl
  have hane : ∀ᶠ x in 𝓝 z, G x i₁ i₁ ≠ 0 := hP.mono fun x hx => (hx.diag_pos (i := i₁)).ne'
  have hdoc : DifferentiableAt ℝ (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z :=
    (hda.inv hane.self_of_nhds).fun_mul hdc
  have h3 : G z i₁ i₁ * dbar (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z ξ
      + dbar (fun x => G x i₁ i₁) z ξ * ((G z i₁ i₁)⁻¹ * G z i₂ i₁) = dbar (fun x => G x i₂ i₁) z ξ := by
    rw [← dbar_mul hda hdoc]
    congr 1
    exact dbar_congr (hane.mono fun x hx => by simp only; field_simp)
  have hb : extForm G z ξ 0 0 = -dbar (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z ξ := by
    rw [extForm_eq_neg_mdbar]
    simp only [Matrix.neg_apply, mdbar_apply, hoc]

  have htr : extTrace G z ξ ξ = kappa * ((quotGram (G z) 0 0)⁻¹ * conj (extForm G z ξ 0 0) * G z i₁ i₁ * extForm G z ξ 0 0) := by
    simp [extTrace, extFormAdj, adj, Matrix.trace_fin_one, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, subGram, Matrix.toBlocks₁₁, i₁]
  have hQ : quotGram (G z) 0 0 = G z i₂ i₂ - G z i₂ i₁ * (G z i₁ i₁)⁻¹ * G z i₁ i₂ := by
    simp [quotGram, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, i₁, i₂]
    rfl
  have hQpos := (Complex.lt_def.1 ((posDef_quotGram hz).diag_pos (i := 0))).1
  have hGb : G z i₁ i₂ = conj (G z i₂ i₁) := (hz.isHermitian.apply i₁ i₂).symm
  have hGd : G z i₂ i₂ = ((G z i₂ i₂).re : ℂ) := by
    have := (Complex.lt_def.1 (hz.diag_pos (i := i₂))).2
    exact Complex.ext (by simp) (by simp [← this])
  rw [diagVal, htr, hQ, hb, h1, h2, hform1 z, hformss, ← h3, hGb, hGd]
  obtain ⟨A, hGa⟩ : ∃ A : ℝ, G z i₁ i₁ = A := ⟨_, hreal.self_of_nhds⟩
  rw [hQ, hGb, hGd] at hQpos
  rw [hGa] at hQpos ⊢
  simp only [ofReal_re] at hQpos ⊢
  have hQC : ((G z i₂ i₂).re : ℂ) - G z i₂ i₁ * (A : ℂ)⁻¹ * conj (G z i₂ i₁) =
      (((G z i₂ i₂).re - normSq (G z i₂ i₁) / A : ℝ) : ℂ) := by
    rw [mul_comm (G z i₂ i₁), mul_assoc, Complex.mul_conj]; push_cast; ring
  rw [hQC] at hQpos ⊢
  rw [Complex.zero_re, ofReal_re] at hQpos
  rw [hGa, ofReal_re] at hApos
  exact proj_rank_two_identity A _ _ _ _ _ _ hApos hQpos

end GlobalTheory.CurveDens
