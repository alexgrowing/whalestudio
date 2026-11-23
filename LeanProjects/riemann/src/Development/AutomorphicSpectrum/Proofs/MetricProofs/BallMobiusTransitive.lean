import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

section Blocks

open scoped MatrixOrder

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem exists_congr_one {A : Matrix a a ℂ} (hA : A.PosDef) : ∃ X : Matrix a a ℂ, Xᴴ * A * X = 1 ∧ IsUnit X.det := by
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hs : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  obtain ⟨C, hCA⟩ : ∃ C : Matrix a a ℂ, A = Cᴴ * C :=
    ⟨CFC.sqrt A, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self A h0]⟩
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit
  have hC : IsUnit C.det := by
    rw [hCA, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  have h1 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hC
  refine ⟨C⁻¹, ?_, ?_⟩
  · calc (C⁻¹)ᴴ * A * C⁻¹ = (C * C⁻¹)ᴴ * (C * C⁻¹) := by
          rw [hCA, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  · exact (Matrix.isUnit_nonsing_inv_det_iff).2 hC

theorem posDef_one_sub_swap {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) : (1 - Wᴴ * W).PosDef := by
  set B := 1 - W * Wᴴ with hB
  have hBu : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hP : (1 + Wᴴ * B⁻¹ * W).PosDef :=
    Matrix.PosDef.one.add_posSemidef (h.inv.posSemidef.conjTranspose_mul_mul_same W)
  have hinv : (1 + Wᴴ * B⁻¹ * W) * (1 - Wᴴ * W) = 1 := by
    have e2 : W * Wᴴ = 1 - B := by rw [hB]; abel
    have e : Wᴴ * B⁻¹ * W * (Wᴴ * W) = Wᴴ * B⁻¹ * (W * Wᴴ) * W := by simp only [Matrix.mul_assoc]
    have e3 : Wᴴ * B⁻¹ * (1 - B) * W = Wᴴ * B⁻¹ * W - Wᴴ * W := by
      have hBi' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc (Wᴴ) (B⁻¹) B, hBi', Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, e, e2, e3]
    abel
  have : (1 - Wᴴ * W) = (1 + Wᴴ * B⁻¹ * W)⁻¹ := (Matrix.inv_eq_right_inv hinv).symm
  rw [this]
  exact hP.inv

theorem exists_boost {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) :
    ∃ u : Matrix (a ⊕ b) (a ⊕ b) ℂ,
      uᴴ * fromBlocks 1 0 0 (-1) * u = fromBlocks 1 0 0 (-1) ∧ u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = W := by
  obtain ⟨X, hX, hXu⟩ := exists_congr_one (posDef_one_sub_swap h)
  obtain ⟨Y, hY, -⟩ := exists_congr_one h
  refine ⟨fromBlocks X (Wᴴ * Y) (W * X) Y, ?_, ?_⟩
  · have e11 : Xᴴ * X - Xᴴ * Wᴴ * (W * X) = 1 := by
      rw [← hX, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have e22 : Yᴴ * W * (Wᴴ * Y) - Yᴴ * Y = -1 := by
      rw [← hY, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.neg_mul]
    congr 1
    · simp only [Matrix.mul_assoc, add_neg_cancel]
    · simp only [Matrix.mul_assoc, add_neg_cancel]
  · have : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXu
    simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁]
    rw [Matrix.mul_assoc, this, Matrix.mul_one]

end Blocks

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem moebBall_transitive : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q → ∃ u : Ψ → Matrix (Sg j j') (Sg j j') ℂ, (∀ τ, IsSgU (u τ)) ∧ moebBall q u 0 = t := by
  intro Ψ _ j j' n q t ht
  have hW : ∀ τ, (1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ).PosDef := by
    intro τ
    have h := (ht τ).transpose
    have e : (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ = 1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
      congr 2
    rwa [e] at h
  choose u hu hm using fun τ => Boost.exists_boost (hW τ)
  refine ⟨u, hu, ?_⟩
  have h0 : ∀ τ, moebW (u τ) (ballMat q 0 τ)ᵀ = (ballMat q t τ)ᵀ := by
    intro τ
    have hz : ballMat q 0 τ = 0 := by
      ext a b
      simp [ballMat]
    rw [hz, moebW, Matrix.transpose_zero, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    exact hm τ
  funext k
  simp only [moebBall, ballPt, h0]
  simp [ballMat]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
