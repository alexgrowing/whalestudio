import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.IsotIndep

theorem gaL_finSum {D : D7} {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c0 : G → ℂ) :
    ∃ (s : Finset (GA D V)) (c : GA D V → ℂ), (∀ g ∈ s, g ∈ GfC V) ∧
      gaL V β L eG c0 = ∑ g ∈ s, c g • principalLevelFrame.rtA g := by
  classical
  let k : G → GA D V := fun g => if hx : ∃ κ, IsLevelLift V β L (eG g) κ then hx.choose else 1
  let a : G → ℂ := fun g =>
    if hx : ∃ κ, IsLevelLift V β L (eG g) κ then c0 g * (levChi V β (flagL L) hx.choose)⁻¹ else 0
  have hk : ∀ g, c0 g • actL V β L (eG g) = a g • principalLevelFrame.rtA (k g) := by
    intro g
    apply LinearMap.ext
    intro F
    funext h
    by_cases hx : ∃ κ, IsLevelLift V β L (eG g) κ
    · have e1 : a g = c0 g * (levChi V β (flagL L) hx.choose)⁻¹ := dif_pos hx
      have e2 : k g = hx.choose := dif_pos hx
      rw [e1, e2]
      show c0 g * actG0 V β L (eG g) F h = c0 g * (levChi V β (flagL L) hx.choose)⁻¹ * F (h * hx.choose)
      unfold actG0
      rw [dif_pos hx, mul_assoc]
    · have e1 : a g = 0 := dif_neg hx
      rw [e1, zero_smul]
      show c0 g * actG0 V β L (eG g) F h = 0
      unfold actG0
      rw [dif_neg hx]
      simp
  refine ⟨Finset.univ.image k, fun x => ∑ g ∈ Finset.univ.filter (fun g => k g = x), a g, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    by_cases h : ∃ κ, IsLevelLift V β L (eG g) κ
    · have e2 : k g = h.choose := dif_pos h
      rw [e2]
      exact h.choose_spec.1
    · have e2 : k g = 1 := dif_neg h
      rw [e2]
      exact one_mem _
  · have e0 : gaL V β L eG c0 = ∑ g, a g • principalLevelFrame.rtA (k g) := by
      unfold gaL
      exact Finset.sum_congr rfl fun g _ => hk g
    rw [e0]
    symm
    calc ∑ x ∈ Finset.univ.image k, (∑ g ∈ Finset.univ.filter (fun g => k g = x), a g) • principalLevelFrame.rtA x
        = ∑ x ∈ Finset.univ.image k, ∑ g ∈ Finset.univ.filter (fun g => k g = x), a g • principalLevelFrame.rtA (k g) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [(Finset.mem_filter.1 hg).2]
      _ = ∑ g, a g • principalLevelFrame.rtA (k g) :=
          Finset.sum_fiberwise_of_maps_to (fun g _ => Finset.mem_image_of_mem k (Finset.mem_univ g)) _

set_option maxHeartbeats 2000000 in

theorem isot_iSupIndep : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ i : Fin D.R.m, iSupIndep (fun σ : D.what₂.FT => D.what₂.isot ((i : ℕ) + 1) σ) := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost i
  have hI : Inputs D := GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra hW hDS hHC hCR D
  have hB := hP.char.base
  have hT := Y.tied.lift
  have h0 := hB.models.νW i
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 false)) h0.1.1 h0.2
  have hO := (GlobalTheory.T.rowFiniteTypes_isotypicParts_span_orthogonal D (Wc D i) _ R.θ (R.MW i (sg0 D A3.A)) (Y.PW i) Y.hF (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) (R.eWf i (sg0 D A3.A)) _ (R.fdW i) hI (D.sp.W_sig _)
    hB.models.inf (Y.stdPsi.2 i) hs.1 hs.2 (gaL_finSum _ _ _ _ _)).2
  apply OrthogonalFamily.independent
  rw [orthogonalFamily_iff_pairwise]
  intro σ σ' hne
  rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hu' := (hT.isot i σ u).1 hu
  have hv' := (hT.isot i σ' v).1 hv
  rw [Y.prtWE] at hu' hv'
  obtain ⟨a, ha, hau⟩ := hu'
  obtain ⟨b, hb, hbv⟩ := hv'
  have hni : ¬ (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ')) := fun h =>
    hne (Y.eFT.injective (principalLevelFrame.rowRepR_inj R.θ _ _ h))
  have key := hO _ _ hni a ha b hb
  rw [hT.mj i u v]
  unfold LiftReal.ipWc ipMT
  rw [← hau, ← hbv]
  refine mul_eq_zero_of_right _ ?_
  refine Eq.trans ?_ key
  congr 1
  · exact LinearEquiv.symm_apply_apply _ a
  · exact LinearEquiv.symm_apply_apply _ b

end GlobalTheory.Mem.R3.IsotIndep
