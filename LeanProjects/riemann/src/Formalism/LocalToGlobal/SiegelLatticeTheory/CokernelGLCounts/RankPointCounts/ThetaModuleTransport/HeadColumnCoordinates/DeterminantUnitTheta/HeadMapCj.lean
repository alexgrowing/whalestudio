import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Asm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem ind_det (hs : M.split = some g) {Z₁ Z₂ : M.Mat (r + 1)} {TT : M.R} (γ : IsoMbe Z₁.Z Z₂.Z)
    (θ θ' : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (h : Ind hs γ θ) (h' : Ind hs γ θ') : θ = θ' := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H l =>
    obtain ⟨l₂, hl₂⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk l))
    exact (h l l₂ hl₂.symm).trans (h' l l₂ hl₂.symm).symm

theorem map_cj_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map M.L.cj = Zh := by
  ext a b; simp [M.L.cj_cj]

theorem det_map_cj {n : Type} [Fintype n] [DecidableEq n] (Zh : Matrix n n E) :
    (Zh.map M.L.cj).det = M.L.cj Zh.det := by
  have := RingHom.map_det (M.L.cj : E →+* E) Zh
  simpa [RingHom.mapMatrix_apply] using this.symm

theorem head_map_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ((Zh.map M.L.cj).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← det_map_cj]
  rfl

theorem gHyp_cj {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z Zσ : M.Mat (r + 1)}
    (h : GHyp M g T T' TT Zh Z Zσ) : GHyp M g T T' TT (Zh.map M.L.cj) Zσ Z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h5, by rw [map_cj_cj]; exact h4, by rw [det_map_cj]; exact h6.map _, ?_⟩
  rw [det_map_cj, head_map_cj, M.L.cj_cj, M.L.cj_cj, mul_comm (M.L.cj Zh.det),
    mul_comm (M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det)]
  exact h7

theorem kapEq_cj {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : KapEq Zh₁ Zh₂) :
    KapEq (Zh₁.map M.L.cj) (Zh₂.map M.L.cj) := by
  unfold KapEq at h ⊢
  rw [det_map_cj, det_map_cj, head_map_cj, head_map_cj, ← map_mul, ← map_mul, h]

end Asm

theorem algGAll_of (hZ : StepZsig) (h0 : StepSplit) (h1 : FirstIsometryForward) (h2 : FirstIsometryBackward) (h3 : FirstIsometryUniqueness)
    (h4 : StepDu) (h5 : StepDuU) : Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic.AlgGAll := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂
  obtain ⟨⟨TT, hTT⟩, hd₁, ⟨Zσ₁, eσ₁⟩⟩ := hZ F E M g hs r T T' hT hq Zh₁ Z₁ e₁ u₁
  obtain ⟨-, hd₂, ⟨Zσ₂, eσ₂⟩⟩ := hZ F E M g hs r T T' hT hq Zh₂ Z₂ e₂ u₂
  let Y₁ : M.Mat (r + 1) := ⟨Z₁, hd₁⟩
  let Y₂ : M.Mat (r + 1) := ⟨Z₂, hd₂⟩
  have H₁ : GHyp M g T T' TT Zh₁ Y₁ Zσ₁ := ⟨hT, hq, hTT, e₁, eσ₁, u₁, hG₁⟩
  have H₂ : GHyp M g T T' TT Zh₂ Y₂ Zσ₂ := ⟨hT, hq, hTT, e₂, eσ₂, u₂, hG₂⟩
  have H₁' := gHyp_cj H₁
  have H₂' := gHyp_cj H₂
  have hrel' := kapEq_cj (M := M) hrel
  show _ = Nat.card (IsoMbe Y₁.Z Y₂.Z)
  rw [h0 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel]
  refine Nat.card_congr
    { toFun := fun p => Classical.choose (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
      invFun := fun γ =>
        ⟨(Classical.choose (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ),
          Classical.choose (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))), by
          have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
          have s4 := Classical.choose_spec (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
          have s2 := Classical.choose_spec (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))
          exact ⟨s1.1, s2.1, s1.2.1, s2.2.1, s4 _ _ s1.2.2 s2.2.2⟩⟩
      left_inv := fun p => by
        have sf := Classical.choose_spec (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
        set γ := Classical.choose (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
        have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        have s4 := Classical.choose_spec (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        have s2 := Classical.choose_spec (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))
        have e1 := ind_det hs γ _ _ s1.2.2 sf
        apply Subtype.ext
        refine Prod.ext e1 ?_
        refine h5 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1 _ _ ?_ p.2.2.2.2.2
        rw [← e1]
        exact s4 _ _ s1.2.2 s2.2.2
      right_inv := fun γ => by
        have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        refine h3 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel _ _ _
          (Classical.choose_spec (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel _ s1.1 s1.2.1))
          s1.2.2 }

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
