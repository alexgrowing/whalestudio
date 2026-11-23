import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCartanDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoshProductDetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameInUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelStabilizerArchStatement

noncomputable section

namespace GlobalTheory.RealDoubling

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

theorem det_cartan {n : ℕ} {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan ε g X) :
    ((2 : ℂ)⁻¹ • (1 + g * gᴴ)).det = ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp X * NormedSpace.exp X)).det := by
  obtain ⟨hX, k₁, k₂, hk₁, hk₂, rfl⟩ := h
  have h2 : k₂ * k₂ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hk₂.1; rwa [Matrix.star_eq_conjTranspose] at this
  have h1 : k₁ * k₁ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hk₁.1; rwa [Matrix.star_eq_conjTranspose] at this
  have h1' : k₁ᴴ * k₁ = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hk₁.1; rwa [Matrix.star_eq_conjTranspose] at this
  have he : (NormedSpace.exp X)ᴴ = NormedSpace.exp X := by
    rw [← Matrix.exp_conjTranspose, hX.1.eq]
  have e : (2 : ℂ)⁻¹ • (1 + k₁ * NormedSpace.exp X * k₂ * (k₁ * NormedSpace.exp X * k₂)ᴴ) =
      k₁ * ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp X * NormedSpace.exp X)) * k₁ᴴ := by
    simp only [Matrix.conjTranspose_mul, he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, h1]
    congr 2
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k₂, h2, Matrix.one_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, h1', Matrix.det_one, one_mul]

theorem gramDet : GramDet := fun n ε g hg =>
  ⟨GlobalTheory.T.exists_cartan_decomposition n ε g hg, fun X hX => (det_cartan hX).trans (GlobalTheory.T.cosh_product_det n ε X hX.1)⟩

theorem rpow_inv_sq {c : ℝ} (hc : 0 < c) (t : ℝ) : ((c ^ 2)⁻¹) ^ t = c ^ (-(2 * t)) := by
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hc.le, Real.rpow_neg hc.le]
  norm_num

theorem doubledAbs : DoubledAbs := by
  intro F E _ _ _ _ _ σ hc n J hJ Q h w τ ε b hb g
  have hI : HasIwasawa σ Q (KArch σ Q w b) := GlobalTheory.Core.Rk.IwArch.hasIwasawa_KArch hc h w b ε hb
  obtain ⟨p, k, hk, e⟩ := hI (ioH _ σ h (g, 1))
  have hU : IsInU ε (inFrame σ J τ b g) := GlobalTheory.T.sign_frame_in_unitary F E σ hc n J w τ ε b hb g
  have key : ∀ X, IsCartan ε (inFrame σ J τ b g) X → ∀ (p' : siegelH w.Completion σ Q) (k' : GArch σ Q w),
      k' ∈ KArch σ Q w b → ioH _ σ h (g, 1) = p' * k' →
      ‖infEmb τ (aH w.Completion σ Q p').1‖ = (coshProd ε X)⁻¹ := by
    intro X hX p' k' hk' e'
    have h1 := GlobalTheory.T.siegel_stabilizer_arch F E σ hc n J hJ.2 Q h w τ b g p' k' hk' e'
    rw [(gramDet n ε _ hU).2 X hX, Complex.norm_real, Real.norm_eq_abs] at h1
    have hc1 := one_le_coshProd ε X
    have hpos : 0 < coshProd ε X := lt_of_lt_of_le one_pos hc1
    rw [abs_of_pos (by positivity)] at h1
    have h2 : ‖infEmb τ (aH w.Completion σ Q p').1‖ ^ 2 = ((coshProd ε X)⁻¹) ^ 2 := by
      field_simp; linarith
    exact (pow_left_inj₀ (norm_nonneg _) (inv_nonneg.2 hpos.le) two_ne_zero).1 h2
  have hval : ∀ X, IsCartan ε (inFrame σ J τ b g) X →
      (hgtArch σ Q w b (ioH _ σ h (g, 1)) : ℝ) = (coshProd ε X ^ 2)⁻¹ := by
    intro X hX
    rw [e, hgtArch_mul hc p hk, absEw_eq_sq hc τ, NNReal.coe_pow, coe_nnnorm, key X hX p k hk e, inv_pow]
  obtain ⟨X0, hX0⟩ := (gramDet n ε _ hU).1
  refine ⟨⟨p, k, hk, e⟩, GlobalTheory.Core.Rk.HgtArch.hgtArch_ioH_le_one hc hJ.2 h b g, ⟨X0, hX0⟩,
    fun X hX => ⟨hval X hX, key X hX, ?_⟩⟩
  intro μ s₀ s Φ hΦ C hC
  have hpos : 0 < coshProd ε X := lt_of_lt_of_le one_pos (one_le_coshProd ε X)
  have hra : hgtH σ Q (absEw F E w) (KArch σ Q w b) (ioH _ σ h (g, 1)) = absEw F E w (aH _ σ Q p) := by
    rw [e]; exact hgtArch_mul hc p hk
  have hr0 : 0 < absEw F E w (aH _ σ Q p) := by rw [← hra]; exact hgtH_pos _
  have hrv : (absEw F E w (aH _ σ Q p) : ℝ) = (coshProd ε X ^ 2)⁻¹ := by rw [← hra]; exact hval X hX
  have hlaw := (mem_degPSH.1 hΦ).1 p k
  have hCk : ‖Φ k‖ ≤ C := hC k hk
  rw [flatArch, flatH_apply, hra, e, hlaw, norm_mul, norm_mul, norm_mul, norm_npow hr0, norm_npow hr0, Circle.norm_coe,
    one_mul, hrv]
  have ht : ((coshProd ε X ^ 2)⁻¹) ^ (s₀ + (n : ℂ) / 2).re * ((coshProd ε X ^ 2)⁻¹) ^ (s - s₀).re =
      coshProd ε X ^ (-(2 * s.re + (n : ℝ))) := by
    rw [← Real.rpow_add (by positivity), rpow_inv_sq hpos]
    congr 1
    simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.natCast_re]
    ring
  calc ((coshProd ε X ^ 2)⁻¹) ^ (s₀ + (n : ℂ) / 2).re * ‖Φ k‖ * ((coshProd ε X ^ 2)⁻¹) ^ (s - s₀).re
      = ‖Φ k‖ * (((coshProd ε X ^ 2)⁻¹) ^ (s₀ + (n : ℂ) / 2).re * ((coshProd ε X ^ 2)⁻¹) ^ (s - s₀).re) := by ring
    _ ≤ C * (((coshProd ε X ^ 2)⁻¹) ^ (s₀ + (n : ℂ) / 2).re * ((coshProd ε X ^ 2)⁻¹) ^ (s - s₀).re) :=
        mul_le_mul_of_nonneg_right hCk (by positivity)
    _ = C * coshProd ε X ^ (-(2 * s.re + (n : ℝ))) := by rw [ht]

theorem realDoublingNorm : RealDoublingNorm := ⟨gramDet, doubledAbs⟩

end GlobalTheory.RealDoubling
