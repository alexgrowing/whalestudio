import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PoiLat

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem quad_mulVec (P : Matrix κ κ ℝ) (W : Matrix κ κ ℂ) (v : κ → ℝ) :
    (fun i => (((P *ᵥ v) i : ℝ) : ℂ)) ⬝ᵥ (W *ᵥ fun i => (((P *ᵥ v) i : ℝ) : ℂ)) =
      (fun i => (v i : ℂ)) ⬝ᵥ
        (((P.map Complex.ofReal)ᵀ * W * P.map Complex.ofReal) *ᵥ fun i => (v i : ℂ)) := by
  rw [GlobalTheory.ofReal_mulVec_eq, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => (v i : ℂ)) ((P.map Complex.ofReal)ᵀ), Matrix.vecMul_transpose]

theorem contragredient_congr {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) (Z : Matrix κ κ ℂ) :
    (((g⁻¹)ᵀ).map Complex.ofReal)ᵀ * Z⁻¹ * ((g⁻¹)ᵀ).map Complex.ofReal =
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹ := by
  have hC : (g⁻¹).map Complex.ofReal = (g.map Complex.ofReal)⁻¹ := (GlobalTheory.inv_map_ofReal hg).symm
  have hC' : ((g⁻¹)ᵀ).map Complex.ofReal = ((g.map Complex.ofReal)⁻¹)ᵀ := by
    rw [Matrix.transpose_map, hC]
  rw [hC', Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem gaussian_lattice_term (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0)
    (a : κ → ℝ) (n : κ → ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z *ᵥ fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
        ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n := by
  have hv : a + g *ᵥ (fun i => (n i : ℝ)) = g *ᵥ ((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg),
      Matrix.one_mulVec, add_comm]
  have hs : (fun i => ((((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) i : ℝ) : ℂ)) =
      ReciprocityTheory.PTheta.shiftVec (g⁻¹ *ᵥ a) n := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  rw [hv, quad_mulVec, hs]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero]
  congr 1
  ring

theorem gaussian_fourier {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) (y : κ → ℝ) :
    ∫ x : κ → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)) =
      GlobalTheory.siegelGaussIntegral Z * Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => (y i : ℂ)) ⬝ᵥ (Z⁻¹ *ᵥ fun i => (y i : ℂ)))) := by
  have hq := hZ.integral_cexp_quadratic (fun i => (y i : ℂ))
  rw [← hq]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  have hxy : ((x ⬝ᵥ y : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (y i : ℂ)) := by
    simp [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hxy]
  ring

theorem siegelGaussIntegral_congr (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) :
    GlobalTheory.siegelGaussIntegral ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) =
      ((|g.det|⁻¹ : ℝ) : ℂ) * GlobalTheory.siegelGaussIntegral Z := by
  have hv : Continuous fun y : κ → ℝ => fun i => (y i : ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hf : Continuous fun y : κ → ℝ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (y i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (y i : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul (hv.dotProduct (continuous_const.matrix_mulVec hv)))
  have key := GlobalTheory.integral_comp_mulVec_of_det_ne_zero hg hf
  simp only [quad_mulVec] at key
  simp only [GlobalTheory.siegelGaussIntegral]
  rw [← abs_inv]
  exact key

theorem fourier_lattice_term {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) {g : Matrix κ κ ℝ}
    (hg : g.det ≠ 0) (n : κ → ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z⁻¹ *ᵥ fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  have hs : ReciprocityTheory.PTheta.shiftVec (0 : κ → ℝ) n = fun i => (((n i : ℝ)) : ℂ) := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  rw [quad_mulVec, contragredient_congr hg]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero, hs, Matrix.neg_mulVec, dotProduct_neg]
  congr 1
  ring

theorem phase_lattice {g : Matrix κ κ ℝ} (a : κ → ℝ) (n : κ → ℤ) :
    ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ) =
      (fun i => (n i : ℂ)) ⬝ᵥ fun i => ((g⁻¹ *ᵥ a) i : ℂ) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem poisson_shifted_lattice : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ), Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ, let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))); let fh : (κ → ℝ) → ℂ := fun y => ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)); Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧ Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧ ∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = ((|g.det|⁻¹ : ℝ) : ℂ) * ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  intro κ _ _ Z hs hp g hg a f fh
  have hZ : GlobalTheory.IsSiegel Z := ⟨hs, hp⟩
  have hσ := hZ.transpose_mul_mul hg
  have hf : ∀ n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n :=
    fun n => gaussian_lattice_term Z hg a n
  have hfh : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) = GlobalTheory.siegelGaussIntegral Z *
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
    intro n
    rw [← fourier_lattice_term hZ hg n]
    exact gaussian_fourier hZ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hf]
    exact hσ.summable_norm_riemannThetaTerm _ _ _
  · simp only [hfh, norm_mul]
    exact (hσ.neg_inv.summable_norm_riemannThetaTerm _ _ _).mul_left _
  · have hterm : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) = GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 (-(g⁻¹ *ᵥ a))
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
      intro n
      rw [hfh, phase_lattice, mul_assoc]
      congr 1
      rw [GlobalTheory.riemannThetaTerm_zero_zero, GlobalTheory.riemannThetaTerm_def, ← Complex.exp_add]
      congr 1
      simp [dotProduct]
      ring
    simp only [hf, hterm]
    rw [tsum_mul_left, ← mul_assoc, ← siegelGaussIntegral_congr Z hg]
    have h0 := hσ.riemannTheta_eq_neg_inv (g⁻¹ *ᵥ a) 0
    have h1 := GlobalTheory.riemannTheta_neg 0 (g⁻¹ *ᵥ a)
      (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0
    simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h0 h1
    rw [h1] at h0
    exact h0

end GlobalTheory.CompanionTheory.SW.Core.PoiLat
