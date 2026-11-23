import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BddInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleModuleInfId
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable abbrev rv (ξ : Fin 2 → ℚ) : Fin 2 → A ℚ := fun i => rt (ξ i)

private noncomputable abbrev sc (a : (A ℚ)ˣ) : GL (Fin 2) (A ℚ) := Matrix.GeneralLinearGroup.scalar (Fin 2) a

private theorem tInv_tInv (x : GL (Fin 2) (A ℚ)) : PositivityTheory.RgEis.tInv (PositivityTheory.RgEis.tInv x) = x := by
  apply Units.ext
  show ((x : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ)ᵀ = x
  rw [Matrix.transpose_transpose]

private theorem tInv_sc (a : (A ℚ)ˣ) : PositivityTheory.RgEis.tInv (sc a) = sc a⁻¹ := by
  apply Units.ext
  show (((sc a)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  rw [← map_inv]
  have e : ((sc a⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = Matrix.diagonal fun _ => ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    rfl
  rw [e, Matrix.diagonal_transpose]

private theorem sc_mulVec (a : (A ℚ)ˣ) (x : GL (Fin 2) (A ℚ)) (v : Fin 2 → A ℚ) :
    ((sc a * x : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ v =
      fun j => (a : A ℚ) * ((x : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ v) j := by
  funext j
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem det_sc (a : (A ℚ)ˣ) : Matrix.GeneralLinearGroup.det (sc a) = a * a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [Matrix.det_fin_two, sq]

private theorem det_tInv (x : GL (Fin 2) (A ℚ)) :
    Matrix.GeneralLinearGroup.det (PositivityTheory.RgEis.tInv x) = (Matrix.GeneralLinearGroup.det x)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

private theorem iy_inv (y : ℝ) (h : y ≠ 0) : iy y⁻¹ = (iy y)⁻¹ := by
  unfold iy
  rw [dif_neg h, dif_neg (inv_ne_zero h), ← map_inv]
  congr 1
  apply Units.ext
  funext _
  rfl

private theorem ab_iy (y : ℝ) (h : y ≠ 0) : ab (iy y) = |y| := by
  unfold ab iy
  rw [dif_neg h]
  have := GlobalTheory.HenQ.DetSplit.ideleModule_infId (K := ℚ) ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩
  rw [this]
  simp

private theorem tsum_split {f : (Fin 2 → ℚ) → ℂ} (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + ∑' ξ : Rw ℚ, f ξ.1 := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton]
  rfl

private theorem poisson_row {Φ : (Fin 2 → A ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhatPi ℚ (Fin 2)) (a : (A ℚ)ˣ)
    (h : GL (Fin 2) (A ℚ)) :
    Summable (fun ξ : Fin 2 → ℚ => Φ fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j) ∧
    Summable (fun ξ : Fin 2 → ℚ => adelicFourierPi ℚ Φ fun j =>
      ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j) ∧
    ∑' ξ : Fin 2 → ℚ, Φ (fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j) =
      ((ab (a * a * Matrix.GeneralLinearGroup.det h) : ℝ) : ℂ)⁻¹ * ∑' ξ : Fin 2 → ℚ, adelicFourierPi ℚ Φ fun j =>
        ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j := by
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 2) (A ℚ), B = sc a * PositivityTheory.RgEis.tInv h⁻¹ := ⟨_, rfl⟩
  have hl := GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem hΦ B
  obtain ⟨h1, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi hl
  have hf := GlobalTheory.CompanionTheory.LtrFourier.adelicFourierPi_ltr B Φ
  have hdet : Matrix.GeneralLinearGroup.det B = a * a * Matrix.GeneralLinearGroup.det h := by
    rw [hB, map_mul, det_sc, det_tInv, map_inv, inv_inv]
  have e1 : ∀ ξ : Fin 2 → ℚ, PositivityTheory.He2M1.ltr B Φ (fun i => algebraMap ℚ (A ℚ) (ξ i)) =
      Φ fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j := by
    intro ξ
    show Φ ((B : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ _) = _
    congr 1
    rw [hB, sc_mulVec]
    funext j
    have e : ((PositivityTheory.RgEis.tInv h⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (h.val)ᵀ := by
      show (((h⁻¹)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
      rw [inv_inv]
    rw [e, Matrix.mulVec_transpose]
  have hBi : PositivityTheory.RgEis.tInv B = sc a⁻¹ * h⁻¹ := by
    rw [hB, map_mul, tInv_sc, tInv_tInv]
  have e2 : ∀ ξ : Fin 2 → ℚ, PositivityTheory.He2M1.ltr (PositivityTheory.RgEis.tInv B) (adelicFourierPi ℚ Φ) (fun i => algebraMap ℚ (A ℚ) (ξ i)) =
      adelicFourierPi ℚ Φ fun j => ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j := by
    intro ξ
    show adelicFourierPi ℚ Φ (((PositivityTheory.RgEis.tInv B : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ _) = _
    congr 1
    rw [hBi, sc_mulVec]
    funext j
    have e : ((PositivityTheory.RgEis.tInv h : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) =
        ((h⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ := rfl
    rw [e, Matrix.vecMul_transpose]
  have hc : ((ab (Matrix.GeneralLinearGroup.det B) : ℝ) : ℂ)⁻¹ ≠ 0 := by
    have : (0 : ℝ) < ab (Matrix.GeneralLinearGroup.det B) := (IdeleGroup.ideleModule ℚ _).2
    exact inv_ne_zero (Complex.ofReal_ne_zero.2 this.ne')
  rw [hf] at h2 h3
  simp only [Pi.smul_apply, smul_eq_mul, e1, e2] at h1 h2 h3
  rw [← hdet]
  refine ⟨h1.of_norm, (summable_mul_left_iff hc).1 h2.of_norm, ?_⟩
  rw [h3, tsum_mul_left]
  rfl

private theorem tInv_dM (u : (A ℚ)ˣ) : PositivityTheory.RgEis.tInv (dM u) = dM u⁻¹ := by
  apply Units.ext
  show (((dM u)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  have e : (((dM u)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![1, 0; 0, ((u⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

private theorem tInv_gl (g : G1 ℚ) : PositivityTheory.RgEis.tInv (gl g) = gl (wW ℚ) * (gl g * (gl (wW ℚ))⁻¹) := by
  have e1 : (gl g)⁻¹ = gl g⁻¹ := (map_inv Matrix.SpecialLinearGroup.toGL g).symm
  have e2 : (gl (wW ℚ))⁻¹ = gl (wW ℚ)⁻¹ := (map_inv Matrix.SpecialLinearGroup.toGL (wW ℚ)).symm
  apply Units.ext
  show (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  have hw : ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, 1; -1, 0] := rfl
  have hwi : (((gl (wW ℚ))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, -1; 1, 0] := by
    rw [e2]
    show Matrix.adjugate (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A ℚ)) = _
    rw [Matrix.adjugate_fin_two]
    simp
  have hgi : (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
    rw [e1]
    show Matrix.adjugate g.1 = _
    rw [Matrix.adjugate_fin_two]
  have hg : ((gl g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![g 0 0, g 0 1; g 1 0, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Units.val_mul, Units.val_mul, hw, hwi, hgi, hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem tInv_h (g : G1 ℚ) (u : (A ℚ)ˣ) :
    PositivityTheory.RgEis.tInv (gl g * dM u) = gl (wW ℚ) * (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
  rw [map_mul, tInv_gl, tInv_dM]
  simp only [mul_assoc]

private theorem det_h (g : G1 ℚ) (u : (A ℚ)ˣ) : Matrix.GeneralLinearGroup.det (gl g * dM u) = u := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul]
  have : ((gl g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)).det = 1 := g.det_coe
  rw [this, one_mul]
  simp [dM, Matrix.det_fin_two]

private def eW : Rw ℚ ≃ Rw ℚ where
  toFun r := ⟨![-(r.1 1), r.1 0], fun h => r.2 (by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    ext i
    fin_cases i <;> simp [h0, h1])⟩
  invFun r := ⟨![r.1 1, -(r.1 0)], fun h => r.2 (by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    ext i
    fin_cases i <;> simp [h0, h1])⟩
  left_inv r := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv r := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

private theorem rv_w (ξ : Fin 2 → ℚ) :
    rv ξ ᵥ* ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = rv ![-(ξ 1), ξ 0] := by
  have hw : ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, 1; -1, 0] := rfl
  rw [hw]
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, UpperTheory.ConvolutionTheory.R2.rt]
  · exact (map_neg (algebraMap ℚ (A ℚ)) (ξ 1)).symm
  · rfl

theorem UpperTheory.thetaSeries_poisson_functional_equation :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi ℚ (Fin 2) → ∃ Ψ ∈ schwartzBruhatPi ℚ (Fin 2), ∀ (t : ℝ) (g : G1 ℚ) (u : (A ℚ)ˣ), ab u = 1 →
        ThR Φ t (gl g * dM u) = -Φ 0 + (Real.exp (-(2 * t)) : ℂ) * Ψ 0 + (Real.exp (-(2 * t)) : ℂ) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
  intro Φ hΦ
  refine ⟨adelicFourierPi ℚ Φ, adelicFourierPi_mem_schwartzBruhatPi hΦ, ?_⟩
  intro t g u hu
  have hne : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  obtain ⟨s1, s2, s3⟩ := poisson_row hΦ (iy (Real.exp t)) (gl g * dM u)
  rw [tsum_split s1, tsum_split s2] at s3
  have hz : rv 0 = 0 := by
    funext i
    show UpperTheory.ConvolutionTheory.R2.rt ((0 : Fin 2 → ℚ) i) = 0
    simp [UpperTheory.ConvolutionTheory.R2.rt]
  have z1 : (fun j => ((iy (Real.exp t) : (A ℚ)ˣ) : A ℚ) * (rv 0 ᵥ* (gl g * dM u).val) j) = 0 := by
    funext j
    simp [hz]
  have z2 : (fun j => (((iy (Real.exp t))⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv 0 ᵥ* (PositivityTheory.RgEis.tInv (gl g * dM u)).val) j) = 0 := by
    funext j
    simp [hz]
  have hd : ab (iy (Real.exp t) * iy (Real.exp t) * Matrix.GeneralLinearGroup.det (gl g * dM u)) = Real.exp (2 * t) := by
    rw [det_h, UpperTheory.ConvolutionTheory.R2.ab_mul, UpperTheory.ConvolutionTheory.R2.ab_mul, hu, ab_iy _ hne, abs_of_pos (Real.exp_pos t), mul_one, ← Real.exp_add, two_mul]
  have hR : ∑' ξ : Rw ℚ, adelicFourierPi ℚ Φ (fun j =>
      (((iy (Real.exp t))⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ.1 ᵥ* (PositivityTheory.RgEis.tInv (gl g * dM u)).val) j) =
      ThR (adelicFourierPi ℚ Φ) (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
    unfold ThR
    refine Eq.trans ?_ (eW.tsum_eq _)
    refine tsum_congr fun ξ => ?_
    congr 1
    funext j
    rw [tInv_h, Units.val_mul, ← Matrix.vecMul_vecMul, rv_w, Real.exp_neg, iy_inv _ hne]
    rfl
  have hL : ∑' ξ : Rw ℚ, Φ (fun j => ((iy (Real.exp t) : (A ℚ)ˣ) : A ℚ) * (rv ξ.1 ᵥ* (gl g * dM u).val) j) =
      ThR Φ t (gl g * dM u) := rfl
  simp only [z1, z2, hR, hL, hd] at s3
  have hexp : ((Real.exp (-(2 * t)) : ℝ) : ℂ) = ((Real.exp (2 * t) : ℝ) : ℂ)⁻¹ := by
    rw [Real.exp_neg, Complex.ofReal_inv]
  rw [hexp]
  linear_combination s3
