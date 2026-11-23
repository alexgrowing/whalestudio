import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInversePropertiesStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section Pure

variable {j j' : ℕ}

theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply, fromBlocks_one]

theorem sgUInv_mul {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    (sgI j j' * uᴴ * sgI j j') * u = 1 := by
  have h : uᴴ * sgI j j' * u = sgI j j' := hu
  calc (sgI j j' * uᴴ * sgI j j') * u = sgI j j' * (uᴴ * sgI j j' * u) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, sgI_mul_self]

theorem mul_sgUInv {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) :
    u * (sgI j j' * uᴴ * sgI j j') = 1 :=
  mul_eq_one_comm.1 (sgUInv_mul hu)

theorem sgUInv_mulVec (u : Matrix (Sg j j') (Sg j j') ℂ) (x : Fin j' → ℂ) :
    (sgI j j' * uᴴ * sgI j j') *ᵥ Sum.elim 0 x =
      Sum.elim (-(u.toBlocks₂₁ᴴ *ᵥ x)) (u.toBlocks₂₂ᴴ *ᵥ x) := by
  conv_lhs => rw [← fromBlocks_toBlocks u]
  simp only [sgI, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_mulVec]
  ext (i | i) <;> simp [Matrix.neg_mulVec, Matrix.mulVec_neg]

theorem mulVec_elim_zero (u : Matrix (Sg j j') (Sg j j') ℂ) (w : Fin j → ℂ) :
    u *ᵥ Sum.elim w 0 = Sum.elim (u.toBlocks₁₁ *ᵥ w) (u.toBlocks₂₁ *ᵥ w) := by
  conv_lhs => rw [← fromBlocks_toBlocks u]
  simp only [fromBlocks_mulVec]
  ext (i | i) <;> simp

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) :
    moebW u 0 = u.toBlocks₂₁ * (u.toBlocks₁₁)⁻¹ := by
  simp [moebW]

theorem star_conj_single (d : Matrix (Fin j') (Fin j') ℂ) (a b : Fin j') :
    star (dᴴ *ᵥ Pi.single a 1) ⬝ᵥ (dᴴ *ᵥ Pi.single b 1) = (d * dᴴ) a b := by
  simp [Matrix.mul_apply, dotProduct, Matrix.mulVec_single_one, Matrix.conjTranspose_apply]

end Pure

section Point

theorem point_graph_gram (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) (W : Matrix (Fin j') (Fin j) ℂ)
    (H1 : ∀ u : Matrix (Sg j j') (Sg j j') ℂ, IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef)
    (H2 : ∀ x y : Fin j' → ℂ, R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y))
    (hA : C.IsAdapted R A) (h0 : (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j')
    (hW : W = moebW (C.cinv (A₀ τ) τ * A τ) 0) :
    (∀ v : Fin j → ℂ, C.pPart R τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) ∧ R.gram (fun b : Fin j' => C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))) * (1 - W * Wᴴ) = ((2 * C.c : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) ∧ (1 - W * Wᴴ).PosDef := by
  obtain ⟨hc1, hc2, -⟩ := GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A₀ τ) h0
  generalize C.cinv (A₀ τ) τ = c at hc1 hc2 hW
  have hsgr : cᴴ * sgI j j' * c = C.sgr τ := by
    have : cᴴ * ((A₀ τ)ᴴ * C.sgr τ * A₀ τ) * c = (A₀ τ * c)ᴴ * C.sgr τ * (A₀ τ * c) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [h0, hc2] at this
    simpa using this
  have hu : IsSgU (c * A τ) := by
    have h : (c * A τ)ᴴ * sgI j j' * (c * A τ) = (A τ)ᴴ * (cᴴ * sgI j j' * c) * A τ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    show (c * A τ)ᴴ * sgI j j' * (c * A τ) = sgI j j'
    rw [h, hsgr, hA.unit τ]
  have hAu : A₀ τ * (c * A τ) = A τ := by
    rw [← Matrix.mul_assoc, hc2, Matrix.one_mul]
  generalize hue : c * A τ = u at hu hAu hW
  obtain ⟨ha, hd, hinv, hpos⟩ := H1 u hu
  rw [← hW] at hinv hpos
  refine ⟨fun v => ?_, ?_, hpos⟩
  · have hWv : Sum.elim v (W *ᵥ v) = u *ᵥ Sum.elim ((u.toBlocks₁₁)⁻¹ *ᵥ v) 0 := by
      rw [mulVec_elim_zero, hW, moebW_zero, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ ha, Matrix.one_mulVec]
    rw [hWv, Matrix.mulVec_mulVec, hAu]
    exact hA.ker τ _
  · have hp : ∀ x : Fin j' → ℂ, C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 x) =
        C.pPart R τ (A τ *ᵥ Sum.elim 0 (u.toBlocks₂₂ᴴ *ᵥ x)) := by
      intro x
      have hA₀ : A₀ τ = A τ * (sgI j j' * uᴴ * sgI j j') := by
        rw [← hAu, Matrix.mul_assoc, mul_sgUInv hu, Matrix.mul_one]
      have hs : (Sum.elim (-(u.toBlocks₂₁ᴴ *ᵥ x)) (u.toBlocks₂₂ᴴ *ᵥ x) : Sg j j' → ℂ) =
          Sum.elim (-(u.toBlocks₂₁ᴴ *ᵥ x)) 0 + Sum.elim (0 : Fin j → ℂ) (u.toBlocks₂₂ᴴ *ᵥ x) := by
        ext (i | i) <;> simp
      conv_lhs => rw [hA₀, ← Matrix.mulVec_mulVec, sgUInv_mulVec, hs, Matrix.mulVec_add]
      rw [pPart_add, hA.ker τ, zero_add]
    have hg : R.gram (fun b : Fin j' => C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))) =
        ((2 * C.c : ℝ) : ℂ) • (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) := by
      ext a b
      simp only [RiemLat.gram, Matrix.of_apply, hp, H2, star_conj_single, Matrix.smul_apply, smul_eq_mul]
    have hinv' : (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) * (1 - W * Wᴴ) = 1 := mul_eq_one_comm.1 hinv
    rw [hg, Matrix.smul_mul, hinv']

end Point

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
