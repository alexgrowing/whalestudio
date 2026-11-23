import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem gramAt_single {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by
  have he : ∀ j : Fin k, embVec σ (Pi.single j 1 : Fin k → K) = Pi.single j 1 := fun j => by
    funext i
    by_cases hij : i = j
    · subst hij; simp [embVec]
    · simp [embVec, hij]
  ext a b
  simp [gramAt, he, mulVec_single, single_dotProduct]

theorem re_mul_of_pos {x : ℂ} (y : ℂ) (hx : 0 < x) : (x * y).re = x.re * y.re := by
  have h := (Complex.pos_iff.mp hx).2
  rw [Complex.mul_re, show x.im = 0 by linarith]
  ring

theorem S6.QuotDegree.proof : S6.QuotDegree.Statement := by
  intro K _ _ n a d ha hd m k b c hli hmk
  set B := sumBasis b c hli hmk
  have hb : (fun i => B (Sum.inl i)) = b := funext fun i => by simp [B, sumBasis_apply]
  have hc : coordProj B ∘ c = fun j : Fin k => (Pi.single j 1 : Fin k → K) := funext fun j => by
    have : c j = B (Sum.inr j) := by simp [B, sumBasis_apply]
    rw [Function.comp_apply, this, KLinesProjLattice.coordProj_basis_inr]
  refine ⟨?_, ?_⟩
  · rw [quotLattice, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      (LinesIdealLatticeFG.full K n a ha).2, Submodule.map_top, LinearMap.range_eq_top]
    exact KLinesQuotIndex.coordProj_surjective B
  · have hspan : Submodule.span K (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) = ⊤ := by
      have h : (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
          Set.range (Pi.basisFun K (Fin k)) := by
        congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
      rw [h]; exact (Pi.basisFun K (Fin k)).span_eq
    have hidx := LinesQuotIndex.full K n m k B (idealLattice a) c
    rw [hb, hc] at hidx
    unfold subDegree quotDegree
    rw [hspan, Submodule.restrictScalars_top, inf_top_eq, hidx]
    congr 2
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [gramAt_single]
    set G := gramAt (diagMetric d σ) σ (Sum.elim b c)
    have hG : G.PosDef := LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli
    have hA : G.toBlocks₁₁.PosDef := hG.submatrix Sum.inl_injective
    have hS : (schurMetric d b c σ).PosDef := schurMetric_posDef hd hli σ
    have hbb : gramAt (diagMetric d σ) σ b = G.toBlocks₁₁ := rfl
    have : Invertible G.toBlocks₁₁ := hA.isUnit.invertible
    have hdet : G.det = G.toBlocks₁₁.det * (schurMetric d b c σ).det := by
      conv_lhs => rw [← fromBlocks_toBlocks G]
      rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
      rfl
    have hApos := hA.det_pos
    have hSpos := hS.det_pos
    rw [hbb, hdet, re_mul_of_pos _ hApos,
      Real.log_mul (Complex.pos_iff.mp hApos).1.ne' (Complex.pos_iff.mp hSpos).1.ne']
    ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
