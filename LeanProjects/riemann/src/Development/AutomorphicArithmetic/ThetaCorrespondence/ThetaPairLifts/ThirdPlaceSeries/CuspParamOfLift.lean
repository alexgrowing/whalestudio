import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowCuspFromLift
theorem exists_isCuspParam_of_liftAt_good_index : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa →
    D.nd.goodRow σ → ∃ π', GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.IsCuspParam D Rw σ π' := by
  intro D Rw hP j σ π μ Pa hL hR hB hm hg
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := hP.tie0.1
  have hAut : SumRepresentations.At.TieAut D.nd D.naut := hP.tie0.2.1
  have hC := hP.cancel
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  obtain ⟨hB1, -, hB3, hB4, hB5, hB6⟩ := hB
  have hpos : ∀ p ∈ twistIso D.nd D.naut L D.naut.etaT, 1 ≤ p.a ∧ 1 ≤ p.d := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hB1 q (hLmem q hq)).1, (hB1 q (hLmem q hq)).2.1⟩
  have hrank : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = D.R.r := by
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    have hr : rankIso D.nd D.naut (L ++ [m]) = D.R.nV := by
      rw [← hB3]; unfold rankIso; exact ((hperm.map _).sum_eq).symm
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hloc : ∀ w, IsSplitPl D.host w →
      isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have e1 := hB4 w hw
    rw [hL.loc w hw, GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append,
      (hLP w (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)
        (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w)
        (D.naut.locG_dim _ w)).1] at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [GlobalTheory.RowThetaParam.isoLoc_cons, GlobalTheory.RowThetaParam.isoLoc_nil, D.naut.lpSum_zero]
      exact GlobalTheory.RowThetaParam.spehLoc_tw D.nd D.naut hLP hC ⟨1, μ, D.R.t⟩ D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, e3,
      (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2]
  obtain ⟨π', hπ'⟩ := GlobalTheory.RowCuspLabels.cusp_of_goodRow D Rw hP.lab σ hg _ hpos hrank hloc
  obtain ⟨q, hLq, hq⟩ := List.map_eq_singleton_iff.1 (show L.map _ = _ from hπ')
  obtain ⟨a, ρ, d⟩ := q
  simp only [Formalism.BasicNotions.Part.mk.injEq] at hq
  obtain ⟨rfl, h2, rfl⟩ := hq
  have h2' := eq_of_heq h2
  subst h2'
  have hmemq : (⟨D.R.r, ρ, 1⟩ : Part D.naut.CG) ∈ l₁ ++ m :: l₂ := hLmem _ (by rw [hLq]; exact List.mem_singleton_self _)
  have hsplit : ∀ w, IsSplitPl D.host w → D.naut.locG (D.naut.tw ρ D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have hs := hloc w hw
    rw [hπ', SphericalInertData.isoLoc_single] at hs
    exact hs
  have hinf : ∀ τ : D.what₂.Tau, D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) ∧
      D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun z => -z) := by
    intro τ
    have eA := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)
    have eB := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).1] at eA
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).2] at eB
    have fA := add_right_cancel eA
    have fB := add_right_cancel eB
    rw [hLq, isoInf_one] at fA fB
    have gA := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1).1
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).2).symm.trans (hL.eta τ).1)
    have gB := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).1).2
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).2).symm.trans (hL.eta τ).2)
    rw [D.naut.infG_tw _ _ _ _ gA, D.naut.infG_tw _ _ _ _ gB, fA, fB]
    simp [Multiset.map_map, Function.comp_def]
  refine ⟨D.naut.tw ρ D.naut.etaT, D.naut.csd_tw ρ D.naut.etaT hAut.1.1 (hB1 _ hmemq).2.2, GlobalTheory.RowRegAlg.ralg_of_infG D _ hinf, hsplit,
    fun w hw => ?_, fun w hw hw' => ?_, hinf⟩
  · have hu := (hB5 w hw).1
    rw [GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.unr_sum, hLq,
      SphericalInertData.isoLoc_single] at hu
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu.1 (D.naut.etaT_unr w)
  · rw [hsplit w hw]
    exact (hR w hw hw').1
end GlobalTheory.RowCuspFromLift
end
end
