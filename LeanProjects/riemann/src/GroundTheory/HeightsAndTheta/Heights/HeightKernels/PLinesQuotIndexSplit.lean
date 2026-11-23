import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace KLinesQuotIndexSplit

theorem colSpan_fg_span (K : Type) [Field K] [NumberField K] (k : ℕ)
    (V : Matrix (Fin k) (Fin k) K) (hV : V.det ≠ 0) :
    ((Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).restrictScalars
        ℤ).FG ∧
      Submodule.span K ((Submodule.span (𝓞 K)
          (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K)) : Submodule (𝓞 K) (Fin k → K)) :
            Set (Fin k → K)) = ⊤ := by
  refine ⟨(Submodule.fg_span (Set.finite_range _)).restrictScalars, ?_⟩
  rw [Submodule.span_span_of_tower]
  have hr : (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K)) =
      (Matrix.mulVecLin V) '' Set.range (Pi.basisFun K (Fin k)) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    simp [Pi.basisFun_apply]
  have hs : Function.Surjective (Matrix.mulVecLin V) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det V).mpr hV.isUnit)
  rw [hr, Submodule.span_image, (Pi.basisFun K (Fin k)).span_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr hs]

end KLinesQuotIndexSplit

open KLinesQuotIndexSplit in

theorem LinesQuotIndexSplit.proof (h1 : LinesQuotIndex.Statement) (h2 : LinesCoordImage.Statement)
    (h3 : LinesCoordDet.Statement) (h4 : LinesIsLattice.Statement)
    (h5 : LinesGenIndexTrans.Statement) (h6 : LinesStdIndexDet.Statement)
    (h7 : LinesProjLattice.Statement) : LinesQuotIndexSplit.Statement := by
  intro K _ _ n m k a B b c τ ha hb hτ hinj hli
  set V := (B.toMatrix (Sum.elim b c)).toBlocks₂₂ with hVdef
  have hdet : V.det ≠ 0 := (h3 K n m k B b c hb hli).2
  have hbB : (fun i => B (Sum.inl i)) = b := funext hb
  have hc : coordProj B ∘ c = fun j => V *ᵥ (Pi.single j 1 : Fin k → K) :=
    funext fun j => h2 K n m k B b c j
  rw [← hbB, h1 K n m k B (idealLattice a) c, hc]
  obtain ⟨hPfg, hPspan, -⟩ := h7 K n m k a B τ ha hτ hinj
  have hP := h4 K (Fin k) _ hPfg hPspan
  have hSfg : ((stdLattice K k).restrictScalars ℤ).FG :=
    (Submodule.fg_span (Set.finite_range _)).restrictScalars
  have hSspan : Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) :
      Set (Fin k → K)) = ⊤ := by
    rw [stdLattice, Submodule.span_span_of_tower]
    have : (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
        Set.range (Pi.basisFun K (Fin k)) := by
      ext v; simp [Pi.basisFun_apply]
    rw [this, (Pi.basisFun K (Fin k)).span_eq]
  have hS := h4 K (Fin k) _ hSfg hSspan
  obtain ⟨hCfg, hCspan⟩ := colSpan_fg_span K k V hdet
  have hC := h4 K (Fin k) _ hCfg hCspan
  have e : genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
        (stdLattice K k).toAddSubgroup *
      genIndex (stdLattice K k).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup =
      genIndex ((idealLattice a).map ((coordProj B).restrictScalars (𝓞 K))).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup :=
    (h5 (Fin k → K) _ _ _ hP hS hC).2
  rw [← e, h6 K k V hdet]

end

end GroundTheory.Heights₂.Heights
