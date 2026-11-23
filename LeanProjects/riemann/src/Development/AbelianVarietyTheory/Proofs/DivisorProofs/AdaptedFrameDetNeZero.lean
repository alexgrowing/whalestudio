import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

theorem GlobalTheory.LineFrame.frame_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d m r s i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E m) (H : Plane E d m), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (hA : H.IsAdapted σ B W W₁ i₀ i₁),
      ((GlobalTheory.JacGeom.frame H.x H.ι H.y).submatrix id (GlobalTheory.LineFrame.frameEquiv hA.rank).symm).det ≠ 0 ∧ W₁.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B d m r s i₀ i₁ W W₁ H hB hW hA
  set e := GlobalTheory.LineFrame.frameEquiv hA.rank with he
  set P := GlobalTheory.JacGeom.frame H.x H.ι H.y with hP
  have hsurj : Function.Surjective (P.submatrix id e.symm).mulVec := by
    have hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ LinearMap.range (Matrix.mulVecLin P) := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨a, b, u, -, -, -, rfl⟩ := hA.split z hz
      exact ⟨Sum.elim (fun _ => a) (Sum.elim u fun _ => b), by
        rw [Matrix.mulVecLin_apply, hP, GlobalTheory.JacGeom.frame_mulVec]⟩
    rw [hW.lat.span_eq_top] at hle
    intro z
    obtain ⟨w, hw⟩ := hle (Submodule.mem_top : z ∈ (⊤ : Submodule E (Fin d → E)))
    refine ⟨w ∘ e.symm, ?_⟩
    rw [Matrix.submatrix_mulVec_equiv]
    simpa [Function.comp_def] using hw
  have hdet : (P.submatrix id e.symm).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 hsurj) |>.ne_zero
  refine ⟨hdet, ?_⟩
  have hG := GlobalTheory.JacGeom.gram_frame hB hW hA
  set Q := P.submatrix id e.symm with hQ
  have hQG : Qᵀ * W.J * Q.map σ = (GlobalTheory.JacGeom.gram W₁.J).submatrix e.symm e.symm := by
    rw [← hG, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id, hQ]
    rfl
  have hσ : (Q.map σ).det = σ Q.det := by
    rw [show σ Q.det = (σ : E →+* E) Q.det from rfl, RingHom.map_det]; rfl
  have hΓ : (GlobalTheory.JacGeom.gram W₁.J).det ≠ 0 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm, ← hQG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hσ]
    refine mul_ne_zero (mul_ne_zero hdet (GlobalTheory.OppLagr.det_ne_zero_skew hW)) ?_
    exact (map_ne_zero_iff _ σ.toRingHom.injective).2 hdet
  intro hJ
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hJ
  apply hΓ
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨Sum.elim 0 (Sum.elim z 0), fun h => hz0 ?_, ?_⟩
  · funext j
    simpa using congrFun h (.inr (.inl j))
  · funext i
    rcases i with i | i | i
    · simp [GlobalTheory.JacGeom.gram, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.fromCols,
        Matrix.fromRows]
    · simpa [GlobalTheory.JacGeom.gram, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.fromCols,
        Matrix.fromRows] using congrFun hz i
    · simp [GlobalTheory.JacGeom.gram, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.fromCols,
        Matrix.fromRows]
