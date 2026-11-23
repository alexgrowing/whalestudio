import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem qsetup_conj_majorant (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (h : QSetup M B ρ P)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hb : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := ((ρ w).map_det B).symm
    rw [e]
    exact (map_ne_zero _).2 h4
  have hd : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have e := congrArg Matrix.det (hg w)
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at e
    exact hb w e.symm
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · intro w
    have hinj : Function.Injective (gi w).mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hd w)))
    have := (h6 w).conjTranspose_mul_mul_same hinj
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · intro w
    set g := gi w with hgdef
    set b := B.map (ρ w) with hbdef
    have hbu : IsUnit b.det := isUnit_iff_ne_zero.2 (hb w)
    have hgw : gᵀ * b * g = b := hg w
    have e1 : (b⁻¹ * gᵀ * b) * g = 1 := by
      rw [Matrix.mul_assoc b⁻¹ gᵀ b, Matrix.mul_assoc b⁻¹, hgw,
        Matrix.nonsing_inv_mul _ hbu]
    have e2 : g * (b⁻¹ * gᵀ * b) = 1 := mul_eq_one_comm.1 e1
    have e3 : (g * b⁻¹ * gᵀ) * b = 1 := by
      rw [← e2]; simp only [Matrix.mul_assoc]
    have e4 : g * b⁻¹ * gᵀ = b⁻¹ := (Matrix.inv_eq_left_inv e3).symm
    calc gᵀ * P w * g * b⁻¹ * (gᵀ * P w * g)
        = gᵀ * P w * (g * b⁻¹ * gᵀ) * P w * g := by simp only [Matrix.mul_assoc]
      _ = gᵀ * (P w * b⁻¹ * P w) * g := by rw [e4]; simp only [Matrix.mul_assoc]
      _ = b := by rw [h7 w, hgw]

end GlobalTheory.CompanionTheory.SW.ThW
