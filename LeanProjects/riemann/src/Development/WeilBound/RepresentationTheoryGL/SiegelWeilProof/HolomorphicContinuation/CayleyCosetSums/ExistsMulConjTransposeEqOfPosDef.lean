import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CRSecB

noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem cT_apply {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) : cT M = Mᴴ := rfl

theorem exists_mul_conjTranspose_eq_of_posDef (Y : Mn n) (hY : Y.PosDef) : ∃ a0 : Mn n, a0 * a0ᴴ = Y ∧ a0.det ≠ 0 := by
  have hA : Y.IsHermitian := hY.1
  set U : Mn n := (hA.eigenvectorUnitary : Mn n) with hU
  set d : Mn n := diagonal (fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)) with hd
  have hsp : Y = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hdd : d * dᴴ = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [hd, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
    rfl
  have hprod : (U * d) * (U * d)ᴴ = Y := by
    calc (U * d) * (U * d)ᴴ = U * (d * dᴴ) * Uᴴ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by rw [hdd, Matrix.star_eq_conjTranspose]
      _ = Y := hsp.symm
  refine ⟨U * d, hprod, fun h0 => ?_⟩
  have hY0 : Y.det ≠ 0 := hY.det_pos.ne'
  apply hY0
  rw [← hprod, det_mul, h0, zero_mul]

theorem inG_diag {b : Mn n} (hb : b.det ≠ 0) : InG (fromBlocks b 0 0 (bᴴ)⁻¹ : M2 n) := by
  have hbH : IsUnit bᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr hb).star
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr hb
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, neg_zero]
  rw [Matrix.mul_nonsing_inv _ hbH, Matrix.nonsing_inv_mul _ hbu]

def bO (a0 V : Mn n) : Mn n := a0 * (1 + imaginary V)

def sec (a0 V : Mn n) : M2 n := (fromBlocks 1 (reP V) 0 1 : M2 n) * fromBlocks (bO a0 V) 0 0 ((bO a0 V)ᴴ)⁻¹

theorem sec_props (a0 V : Mn n) (hb : (bO a0 V).det ≠ 0) :
    InG (sec a0 V) ∧ (sec a0 V).det ≠ 0 ∧ zOfE (sec a0 V) = fM a0 V := by
  have hbH : IsUnit (bO a0 V)ᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr hb).star
  refine ⟨inG_mul (inG_upper (reP_herm V)) (inG_diag hb), ?_, ?_⟩
  · unfold sec
    rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul, det_nonsing_inv]
    refine mul_ne_zero hb ?_
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (isUnit_iff_ne_zero.mp hbH)
  · have hs : sec a0 V = fromBlocks (bO a0 V) (reP V * ((bO a0 V)ᴴ)⁻¹) 0 ((bO a0 V)ᴴ)⁻¹ := by
      unfold sec; rw [fromBlocks_multiply]; simp
    unfold zOfE u1
    rw [hs]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero,
      zero_add]
    rw [Matrix.nonsing_inv_nonsing_inv _ hbH, Matrix.add_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbH,
      Matrix.mul_one, Matrix.smul_mul]
    unfold fM bO
    have hB : (1 + imaginary V)ᴴ = 1 + imaginary V := by rw [conjTranspose_add, conjTranspose_one, imaginaryPart_isHermitian]
    rw [conjTranspose_mul, hB, add_comm]
    simp only [Matrix.mul_assoc]

theorem locSec : LocSec := by
  intro n Z0 hY
  obtain ⟨a0, ha0, hdet⟩ := exists_mul_conjTranspose_eq_of_posDef _ hY
  set V0 : Mn n := reP Z0 with hV0def
  have hV0 : V0ᴴ = V0 := reP_herm Z0
  have hfV0 : fM a0 V0 = Z0 := by
    unfold fM
    rw [imaginaryPart_of_isHermitian hV0, reP_of_herm hV0, add_zero, Matrix.mul_one, Matrix.mul_one, ha0]
    exact reP_add_imP Z0
  have hcd : ContDiffAt ℝ ⊤ (fM a0) V0 := (contDiff_fM a0).contDiffAt
  have hd : DifferentiableAt ℝ (fM a0) V0 := ((contDiff_fM a0).differentiable (by simp)).differentiableAt
  let e : Mn n ≃L[ℝ] Mn n :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (fM a0) V0 : Mn n →ₗ[ℝ] Mn n)
      (fderiv_fM_inj a0 V0 hV0 hdet)).toContinuousLinearEquiv
  have he : (e : Mn n →L[ℝ] Mn n) = fderiv ℝ (fM a0) V0 := by ext1 x; rfl
  have hf' : HasFDerivAt (fM a0) (e : Mn n →L[ℝ] Mn n) V0 := by rw [he]; exact hd.hasFDerivAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set g := hcd.localInverse hf' hn with hgdef
  have hg : ContDiffAt ℝ ⊤ g (fM a0 V0) := hcd.to_localInverse hf' hn
  have hgV : g (fM a0 V0) = V0 := hcd.localInverse_apply_image hf' hn
  have hright : ∀ᶠ Z in 𝓝 (fM a0 V0), fM a0 (g Z) = Z := (hcd.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  rw [hfV0] at hg hgV hright
  have hg1 : ContDiffAt ℝ 1 g Z0 := hg.of_le le_top
  have hre : ContDiffAt ℝ 1 (fun Z => reP (g Z)) Z0 := reL.contDiff.contDiffAt.comp Z0 hg1
  have him : ContDiffAt ℝ 1 (fun Z => imaginary (g Z)) Z0 := imL.contDiff.contDiffAt.comp Z0 hg1
  have hbo : ContDiffAt ℝ 1 (fun Z => bO a0 (g Z)) Z0 := contDiffAt_mul' contDiffAt_const (contDiffAt_const.add him)
  have hbZ0 : bO a0 (g Z0) = a0 := by rw [hgV, bO, imaginaryPart_of_isHermitian hV0, add_zero, Matrix.mul_one]
  have hbH0 : ((bO a0 (g Z0))ᴴ).det ≠ 0 := by
    rw [hbZ0, det_conjTranspose]; exact (star_ne_zero).mpr hdet
  have hcT : ContDiffAt ℝ 1 (fun Z => (bO a0 (g Z))ᴴ) Z0 := by
    have h := cT.contDiff.contDiffAt.comp Z0 hbo
    simp only [Function.comp_def] at h
    exact h
  have hinv : ContDiffAt ℝ 1 (fun Z => ((bO a0 (g Z))ᴴ)⁻¹) Z0 :=
    (contDiffAt_inv ((bO a0 (g Z0))ᴴ) hbH0).comp Z0 hcT
  have hcont : ContinuousAt (fun Z => (bO a0 (g Z)).det) Z0 :=
    (continuous_id.matrix_det.continuousAt).comp hbo.continuousAt
  have hev : ∀ᶠ Z in 𝓝 Z0, (bO a0 (g Z)).det ≠ 0 :=
    hcont.eventually_ne (by simp only [hbZ0]; exact hdet)
  refine ⟨fun Z => sec a0 (g Z), ?_, ?_⟩
  · filter_upwards [hright, hev] with Z hZ hb
    obtain ⟨h1, h2, h3⟩ := sec_props a0 (g Z) hb
    exact ⟨h1, h2, h3.trans hZ⟩
  · unfold sec
    exact contDiffAt_mul' (contDiffAt_fromBlocks contDiffAt_const hre contDiffAt_const contDiffAt_const)
      (contDiffAt_fromBlocks hbo contDiffAt_const contDiffAt_const hinv)

end PositivityTheory.Rg.Sw.HSt.CRSec

namespace PositivityTheory.Rg.Sw.HSt

theorem locSec : LocSec := CRSec.locSec

end PositivityTheory.Rg.Sw.HSt
