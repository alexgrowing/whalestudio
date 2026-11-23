import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPJFMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLJCommC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Help

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rdsp_rw_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (w : List (B.Mat k r)) :
    ∀ g, g ∉ tsupport F → B.Rw w F g = 0 := by
  intro g hg
  rw [Formalism.FourierDecayAlt.P.JCTx6.Pos.rw_congr_open (isClosed_tsupport F).isOpen_compl (f₁ := F) (f₂ := 0)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) w g hg, Formalism.FourierDecayAlt.P.CutMP.JA.GA.rw_zero_fn]
  rfl

theorem rdsp_tsupport_sub {E E' : Type*} [Zero E] [Zero E'] {G : B.Mat k r → E} {F : B.Mat k r → E'}
    (h : ∀ g, g ∉ tsupport F → G g = 0) : tsupport G ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro g hg
  by_contra hc
  exact hg (h g hc)

variable [FiniteDimensional ℂ Wq]

theorem rdsp_opApply_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opApply Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opApply
  have h0 : ∀ T ∈ Θ, T.coef g (B.Rw T.word F g) = 0 := by
    intro T _
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz T.word g hg, map_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

theorem rdsp_opAdj_vanishP (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ g, g ∉ tsupport F → B.opAdj Θ F g = 0 := by
  have hz : ∀ x ∈ (tsupport F)ᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport F (Function.mem_support.mpr hne))
  intro g hg
  unfold Formalism.FourierDecayAlt.B.opAdj
  have h0 : ∀ T ∈ Θ, ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g = 0 := by
    intro T _
    have hz' : ∀ x ∈ (tsupport F)ᶜ, T.coefAdj x (F x) = 0 := by
      intro x hx
      rw [hz x hx, map_zero]
    rw [Formalism.FourierDecayAlt.P.Ux8.Rw_vanish (isClosed_tsupport F).isOpen_compl hz' T.word.reverse g hg, smul_zero]
  first
    | (apply List.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
       exact h0 T hT)
    | (apply Multiset.sum_eq_zero
       intro x hx
       obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
       exact h0 T hT)

end Help

theorem spectral_pairing_operator : RDSPOp := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hS hC F hF hFc hFO
  have hOP : tsupport F ⊆ B.GPos D := fun g hg => ⟨(hFO hg).1, (hFO hg).2.2⟩
  have hsuppF : B.SuppIn (B.GPos D) F :=
    (closure_mono (fun g hg => hg.2)).trans ((closure_minimal subset_closure (isClosed_tsupport F)).trans hOP)
  have hA1t : tsupport (B.opApply Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opApply_vanishP Θ F)
  have hB1t : tsupport (B.opAdj Θ F) ⊆ tsupport F := rdsp_tsupport_sub (rdsp_opAdj_vanishP Θ F)
  have hA1s : B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) := by
    refine Formalism.FourierDecayAlt.P.PBJ.ckOn_opApply_list (B.GPos D) F hF hsuppF Θ (fun T hT => (hS T hT).1) fun T _ => ?_
    refine (closure_minimal (fun g hg => ?_) (isClosed_tsupport F)).trans hOP
    by_contra hgF
    exact hg.2 (rdsp_rw_vanish F T.word g hgF)
  have hB1s : B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.ckOn_opAdj D Θ hS hF hsuppF
  refine ⟨⟨hA1s, hFc.of_isClosed_subset (isClosed_tsupport _) hA1t, hA1t⟩,
    ⟨hB1s, hFc.of_isClosed_subset (isClosed_tsupport _) hB1t, hB1t⟩, ?_⟩

  have hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ tsupport F, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g := by
    rcases (tsupport F).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨g₀, hg₀, hmin⟩ := hFc.exists_isMinOn h (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont D.z D.z').continuousOn
      exact ⟨_, (hFO hg₀).2.2, fun g hg => isMinOn_iff.mp hmin g hg⟩
  obtain ⟨ε, hε, hεG⟩ := hpos
  have hCk : B.CkOn ⊤ (JF.Om k r D.z D.z') (B.JF D F) :=
    (radial_orbital_niceness k r Wp Wq D F ⟨ε, hε, hF, fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc
      (fun g _ hg => image_eq_zero_of_notMem_tsupport hg) A m,
      fun g _ hg => hεG g (subset_tsupport F hg)⟩).2
  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (r : ℝ) * (B.opOrder Θ : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds k r Wp Wq D Θ _ F
    (JF.Om k r D.z D.z') (Formalism.FourierDecayAlt.P.CutMP.JA.SA.thrW_sa k r (B.opOrder Θ)) hS hC hF hIn subset_rfl
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hCk)
  exact fun g hg => ⟨hT1 g hg, hT2 g hg⟩

end Formalism.FourierDecayAlt.P.CutSE
