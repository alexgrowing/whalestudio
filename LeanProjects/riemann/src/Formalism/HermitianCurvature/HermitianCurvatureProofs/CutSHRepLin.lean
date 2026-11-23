import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem repLin_nice {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp))
    (hG : GoodFam T j G) (t : ℂ) (ht : t ≠ 0) :
    ∃ ε, 0 < ε ∧ JC.NiceCoef (T.bs (j + 1)) ε (G t) := by
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 {t} isCompact_singleton (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact ht)
  have hsupp : ∀ γ, G t γ ≠ 0 → γ ∈ C := fun γ h => (hCε t rfl γ h).1
  have hck : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t ht γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  exact ⟨ε, hε, hck, fun A' m' => JFxG.cptInCC_G hck hC (fun γ _ hγC => by
      by_contra h; exact hγC (hsupp γ h)) A' m', fun γ hγ hne => (hCε t rfl γ hne).2 hγ⟩

theorem representation_linear : RepLin := by
  intro Wp Wq _ _ _ _ _ _ P T _ _ j _ _ G G' hG hG' t ht a x hx
  obtain ⟨ε, hε, hN⟩ := repLin_nice T j G hG t ht
  obtain ⟨ε', hε', hN'⟩ := repLin_nice T j G' hG' t ht
  have hm : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G t) :=
    ⟨hN.1, hN.2.1, fun g hg hne => (min_le_left _ _).trans (hN.2.2 g hg hne)⟩
  have hm' : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G' t) :=
    ⟨hN'.1, hN'.2.1, fun g hg hne => (min_le_right _ _).trans (hN'.2.2 g hg hne)⟩
  have hom : wCell P.k (P.r - (j + 1)) (Fin.last (P.r - (j + 1))) x.1 * x.2 ∈
      JF.Om P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' :=
    TLB.wCell_om (Pa := JC.parLev P (j + 1)) (T.bs (j + 1)) hx
  have hs : B.JF (T.bs (j + 1)) (fun γ => a • G t γ) = a • B.JF (T.bs (j + 1)) (G t) :=
    funext fun h => JCx2.bc_JF_smul a (G t) h
  refine ⟨?_, ?_⟩
  · simp only [resG]
    rw [JCx2.bc_JF_add hm hm' hom, smul_add]
  · rw [hs, JCx2.rma_resG_smul]

end Formalism.FourierDecayAlt.P.CutSH
