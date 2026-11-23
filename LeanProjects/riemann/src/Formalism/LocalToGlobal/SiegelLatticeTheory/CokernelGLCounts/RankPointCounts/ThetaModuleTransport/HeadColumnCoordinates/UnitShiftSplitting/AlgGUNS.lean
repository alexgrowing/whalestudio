import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.HeadMapCj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaMbe0GOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.SelfDualLatticesOneOrbit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.HatZSecondProjTranspose
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.StepLiftG

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

def AlgGAllNS : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] → IsUnit (Z₁.map M.R.subtype).det → IsUnit (Z₂.map M.R.subtype).det →
    IsUnit (HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T').det → IsUnit (HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T').det →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

theorem algGAllNS_of (h0 : StepSplit) (h1 : FirstIsometryForward) (h2 : FirstIsometryBackward) (h3 : FirstIsometryUniqueness)
    (h4 : StepDu) (h5 : StepDuU) : AlgGAllNS := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂ hT0 hd₁ hd₂ hσ₁ hσ₂
  obtain ⟨c, hc⟩ := hq
  have hT'0 : T' ∈ 𝒪[F] := by
    have : T' = T - (g.q : F) ^ 2 * c := by rw [← hc]; ring
    rw [this]
    exact sub_mem hT0 (mul_mem (pow_mem g.q.2 2) c.2)
  have hq : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c := ⟨c, hc⟩
  let TT : M.R := ⟨g.e.symm (T, T'), mem_R_of hs _ ⟨T, hT0⟩ ⟨T', hT'0⟩ (g.q * c) (by simp)
    (by push_cast; rw [hc]; ring)⟩
  have hTT : g.e (TT : E) = (T, T') := by simp [TT]
  let Zs₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R :=
    Matrix.of fun a b => ⟨_, zsig_mem hs T T' c hc Zh₁ Z₁ e₁ a b⟩
  have eZs₁ : Zs₁.map M.R.subtype = HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T' := by ext a b; rfl
  let Zs₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R :=
    Matrix.of fun a b => ⟨_, zsig_mem hs T T' c hc Zh₂ Z₂ e₂ a b⟩
  have eZs₂ : Zs₂.map M.R.subtype = HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T' := by ext a b; rfl
  let Zσ₁ : M.Mat (r + 1) := ⟨Zs₁, by rw [eZs₁]; exact hσ₁⟩
  let Zσ₂ : M.Mat (r + 1) := ⟨Zs₂, by rw [eZs₂]; exact hσ₂⟩
  have eσ₁ : Zσ₁.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T' := eZs₁
  have eσ₂ : Zσ₂.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T' := eZs₂
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

theorem algGAllNS_holds : AlgGAllNS :=
  algGAllNS_of stepSplit_holds firstIso_forward_holds firstIso_backward_holds firstIso_uniqueness_holds (stepDu_of_lift stepLiftG) stepDuU

end Formalism.L2.SG.LocalCountModules.AlgGSplit
