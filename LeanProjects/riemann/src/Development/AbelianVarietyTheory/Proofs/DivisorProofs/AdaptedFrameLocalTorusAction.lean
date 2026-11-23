import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplMapSplitProj

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

noncomputable section

namespace GlobalTheory.LeviFrameSplit

theorem leviEmb_positionOne_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {d : ℕ} (h2 : 2 ≤ d) (y : kˣ) :
    ((leviEmb k (linePlace h2) (firstBlockScalar k d y) : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) =
      Matrix.diagonal fun j : Fin d => if (j : ℕ) = 0 then (y : k) else 1 := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (linePlace h2).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (linePlace h2).surjective j
  have hv := GlobalTheory.BlockForms.LeviLoc.tripPlace_val (l := 1) (d := d - 2) (n := d) (by omega) a i
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      by_cases ha : a = 0
      · subst ha
        have hi := i.2
        simp only [tripSizes, Matrix.cons_val_zero] at hi
        have hv0 : ((linePlace h2 ⟨0, i⟩ : Fin d) : ℕ) = 0 := by
          rw [hv]; simp; omega
        rw [if_pos hv0]
        simp [firstBlockScalar]
      · have h1 : 1 ≤ (![0, 1, 1 + (d - 2)] : Fin 3 → ℕ) a := by
          fin_cases a <;> simp_all
        have hv1 : ((linePlace h2 ⟨a, i⟩ : Fin d) : ℕ) ≠ 0 := by
          rw [hv]; omega
        rw [if_neg hv1]
        simp [firstBlockScalar, Pi.mulSingle_eq_of_ne ha]
    · rw [Matrix.diagonal_apply_ne _ ((linePlace h2).injective.ne fun h => hij (eq_of_heq (Sigma.mk.inj_iff.1 h).2))]
      by_cases ha : a = 0
      · subst ha
        simp [firstBlockScalar, hij]
      · simp [firstBlockScalar, Pi.mulSingle_eq_of_ne ha, Matrix.one_apply_ne hij]
  · rw [leviEmb_apply_ne _ _ _ hab, Matrix.diagonal_apply_ne _
      ((linePlace h2).injective.ne fun h => hab (congrArg Sigma.fst h))]

end GlobalTheory.LeviFrameSplit

namespace GlobalTheory.LeviFrameSplit

open GlobalTheory.Div.CoordOpp (piW_inclR piW_cA incM_map_piW)

theorem levi_frame_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d m i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E m) (H : Plane E d m) (hcm : IsCMExt F E σ)
    (hA : H.IsAdapted σ B W W₁ i₀ i₁),
      ((GlobalTheory.JacGeom.frame H.x H.ι H.y).submatrix id (GlobalTheory.LineFrame.frameEquiv hA.rank).symm).det ≠ 0 →
      ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (h2 : 2 ≤ d) (y : (Fv F v)ˣ) (g : UA σ W.J),
        IsLevi (W₁ := W₁) H (GlobalTheory.JacGeom.idl hcm t (y, 1)) 1 g →
        (mat g).map (piW t) = ((GlobalTheory.LineFrame.frameGL t H hA.rank * leviEmb (Fv F v) (linePlace h2) (firstBlockScalar (Fv F v) d y) *
          (GlobalTheory.LineFrame.frameGL t H hA.rank)⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d m i₀ i₁ W W₁ H hcm hA hdet v t h2 y g hL
  obtain ⟨hx, hy, hι⟩ := hL
  set A := (mat g).map (piW t) with hAdef
  have cx : ∀ r, ∑ k, A r k * t (H.x k) = (y : Fv F v) * t (H.x r) := fun r => by
    have := congrArg (piW t) (congrFun hx r)
    rw [RingHom.map_mulVec] at this
    simpa [Matrix.mulVec, dotProduct, GlobalTheory.ThK.incV, piW_inclR, GlobalTheory.JacGeom.piW_idl, A] using this
  have cy : ∀ r, ∑ k, A r k * t (H.y k) = t (H.y r) := fun r => by
    have := congrArg (piW t) (congrFun hy r)
    rw [RingHom.map_mulVec] at this
    have e1 : ((GlobalTheory.JacGeom.idl hcm t (y, 1))⁻¹ : (AE F E)ˣ) = GlobalTheory.JacGeom.idl hcm t (y⁻¹, 1) := by
      rw [← map_inv, Prod.inv_mk, inv_one]
    rw [e1] at this
    simpa [Matrix.mulVec, dotProduct, GlobalTheory.ThK.incV, piW_inclR, piW_cA, GlobalTheory.JacGeom.piW_comp_idl, A] using this
  have cι : A * H.ι.map t = H.ι.map t := by
    have := congrArg (fun Z => Z.map (piW t)) hι
    simp only [Matrix.map_mul, incM_map_piW] at this
    rw [show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    exact this
  have hPe : ∀ r c, frameMat t H hA.rank r (frameEquiv hA.rank c) = t (GlobalTheory.JacGeom.frame H.x H.ι H.y r c) :=
    fun r c => by simp only [frameMat, Matrix.submatrix_apply, Matrix.map_apply, id, Equiv.symm_apply_apply]
  have key : A * frameMat t H hA.rank =
      frameMat t H hA.rank * Matrix.diagonal fun j : Fin d => if (j : ℕ) = 0 then (y : Fv F v) else 1 := by
    refine Matrix.ext fun r j => ?_
    obtain ⟨c, rfl⟩ := (frameEquiv hA.rank).surjective j
    rw [Matrix.mul_diagonal, Matrix.mul_apply, hPe]
    rcases c with (i | i | i)
    · rw [if_pos (frameEquiv_inl hA.rank i)]
      simp only [hPe, GlobalTheory.JacGeom.frame, Matrix.of_apply, Sum.elim_inl]
      rw [cx r, mul_comm]
    · have hv : ((frameEquiv hA.rank (.inr (.inl i)) : Fin d) : ℕ) ≠ 0 := by rw [frameEquiv_mid]; omega
      rw [if_neg hv, mul_one]
      simp only [hPe, GlobalTheory.JacGeom.frame, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
      have := congrFun (congrFun cι r) i
      simpa only [Matrix.mul_apply, Matrix.map_apply] using this
    · have hv : ((frameEquiv hA.rank (.inr (.inr i)) : Fin d) : ℕ) ≠ 0 := by rw [frameEquiv_inr]; omega
      rw [if_neg hv, mul_one]
      simp only [hPe, GlobalTheory.JacGeom.frame, Matrix.of_apply, Sum.elim_inr]
      exact cy r
  have hU : IsUnit (frameMat t H hA.rank) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    change (((GlobalTheory.JacGeom.frame H.x H.ι H.y).submatrix id (frameEquiv hA.rank).symm).map (t : E →+* Fv F v)).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hdet
  have hc : frameMat t H hA.rank * ((frameGL t H hA.rank)⁻¹ : GL (Fin d) (Fv F v)) = 1 := by
    rw [← frameGL_val t H hA.rank hU]; exact Units.mul_inv _
  rw [Units.val_mul, Units.val_mul, frameGL_val t H hA.rank hU, leviEmb_positionOne_eq, ← key, Matrix.mul_assoc, hc,
    Matrix.mul_one]

end GlobalTheory.LeviFrameSplit
