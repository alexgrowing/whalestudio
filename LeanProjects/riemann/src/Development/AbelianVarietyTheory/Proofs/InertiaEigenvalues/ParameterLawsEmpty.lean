import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricRigidOfPin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm7OfAutomorphicCsdTemperedPurity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.ParLawsBare

open GlobalTheory.RowTie GlobalTheory.NPin Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem heckeCharTie_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) :
    GlobalTheory.HeckeSplitRow.HeckeCharTie D.nd D.naut :=
  ⟨fun π => (cs.e1 π).1, fun _ _ h => cs.e1.injective (Subtype.ext h), cs.unr_iff, cs.frob⟩

theorem heckeSplitOne_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) : GlobalTheory.RowCopy.HeckeSplitOne D :=
  fun ν ν' hw => GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut (heckeCharTie_of_side cs) ν ν' hw

theorem cancel_of_tie {D : D7} (T : WDTie D.nd D.naut) :
    ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b := by
  intro w a b c h
  apply (T.e w).injective
  refine GlobalTheory.WeilDeligne.WD.lpSum_cancel_right _ _ _ _ _ _ _ (T.e w c) ?_
  rw [← T.sum, ← T.sum, h]

open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil in

theorem locG_rankOne_eq_rcAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = rcAt hL D w 1 (GlobalTheory.SplitRead.Irr.ofDet 1 ξ h.1) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = GlobalTheory.CuspRep.ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ w, fun x => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, GlobalTheory.CuspRep.ParLaws.locPar_ofChar, rcAt]
  rw [hchar]
  rfl

open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil in

theorem rankOneUnitary {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (cs : CharSide D cf) : RankOneUnitary T := by
  intro π w σ _ α hα
  obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.HeckeComp.main D.host.E (cs.e1 π).1 w
  have he := locG_rankOne_eq_rcAt T cg cs π w ξ hξ
  rw [WDTie.eig, he] at hα
  unfold WD.inePol at hα
  split_ifs at hα with hσ
  · exact GlobalTheory.LocLanglands.IsRec.recUnit (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) ξ
      (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1) (hξu (cs.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα
  · simp at hα

open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL in

theorem rankTwo (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : GlobalTheory.Published.CohomologicalCsdTempered)
    (hRP : GlobalTheory.Published.RegularAlgebraicPurity) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : WDTie D.nd D.naut)
    (cg : CGTrue hL D T) (a : ℕ) (π : D.naut.CG a) (ha : 2 ≤ a) (hc : D.naut.csd π) (hr : D.naut.ralg π)
    (w : PlE D.host) : D.naut.tempered (D.naut.locG π w) := by
  have := host_isCMField D.host
  have ha1 : 1 ≤ a := by omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (cg.e a π).1
  have hmk : CG.mk π₀ = (cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  have hcoh := (hRP D.host.E a ha1 π₀ hr₀).2
  obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hAF D.host.E a π₀ w
  have htG := hT D.host.E a ha π₀ hc₀ hcoh w σ₀ hσ₀
  rw [T.tempered, cg.loc]
  show (GlobalTheory.CuspRep.ParLaws.locPar hL (cg.e a π).1 (D.nd.plOm.2 w)).tempered
  rw [← hmk, GlobalTheory.CuspRep.ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
  exact GlobalTheory.T.tempered_rep_tempered_parameter D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) a
    (GlobalTheory.CuspRep.ParLaws.toRep σ₀) htG

theorem tieAut_of_side {D : D7} {cf : CharFrame D} (cs : CharSide D cf) (hE : IsEmpty D.nd.Loc) :
    Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut := by
  have hcsd : IsCSD D.host cf.eta := GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ cf.isEta
  have hE1 : (cs.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [cs.etaT]; exact cf.isEta.inf⟩
  have hE' : (cs.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => (-(1 / 2) : ℚ)) :=
    ⟨fun _ => -1, fun _ => by norm_num, by rw [cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.hasInf_inv cf.isEta.inf⟩
  refine ⟨⟨?_, ?_⟩, fun τ => ?_, fun w => ?_, fun i _ => isEmptyElim i⟩
  · rw [cs.csd, cs.etaT]; exact hcsd
  · rw [cs.csd, cs.etaTinv]; exact GlobalTheory.AutomorphismSplitting.isCSD_inv' hcsd
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
    · have ht : τ = embPsi D.host (D.eTau ρ) := h.symm
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).1, (cs.infG _ _ hE' (D.eTau ρ)).1]
      refine ⟨Or.inl (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; rfl
    · have ht : τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) := by
        rw [← h]; ext x; rfl
      rw [ht, (cs.infG _ _ hE1 (D.eTau ρ)).2, (cs.infG _ _ hE' (D.eTau ρ)).2]
      refine ⟨Or.inr (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; ring_nf
  · have hu : D.naut.unr (D.naut.locG D.naut.etaT w) := D.naut.etaT_unr w
    rw [D.naut.tempered_unr _ hu, cs.frob _ w ((cs.unr_iff _ w).1 hu)]
    intro α hα
    rw [Multiset.mem_singleton] at hα
    subst hα
    have h1 : ‖(((cs.e1 D.naut.etaT).1.val w : ℂˣ) : ℂ)‖ = 1 := (cs.e1 D.naut.etaT).2 _
    rw [Units.val_inv_eq_inv_val, norm_inv, h1, inv_one]

theorem tieGal_bare {D : D7} (hE : IsEmpty D.nd.Loc) : Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

theorem tieLab_of_lab {D : D7} (T : WDTie D.nd D.naut) (lab : LabTrue D T) : Formalism.MainNotions.SumRepresentations.tieLab D := by
  let γ : Fin 2 → PlE D.host → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om :=
    fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1)
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  have hT : GlobalTheory.LabLaws.LabTie T D.ntypes.teichC γ := by
    intro k v
    rw [hγ k v]
    exact ⟨D.ntypes.teichC_inj k, D.ntypes.tg_gen k v, lab k v⟩
  exact GlobalTheory.LabLaws.tieLab_of_labTie hT

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ (D : D7) (cf : CharFrame D) rep Rw,
    IsEmpty D.nd.Loc → ParIn hL D cf rep Rw → ParLaws D := by
  intro hP hL D cf rep Rw hE X
  have hrig : IsobaricRigid D.nd D.naut := by
    have := GlobalTheory.CuspRep.host_isCMField D.host
    exact GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hP.what₂.js.1 (GlobalTheory.HeightCounting.Blocks.readsCusp hP.what₂.fin X.cg)
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D X.T, tieAut_of_side X.chr hE, tieGal_bare hE⟩
  have ha7 : Formalism.MainNotions.SumRepresentations.adm7 D :=
    GlobalTheory.RowTie.admissible_of_rank_one_unitary D X.T (rankOneUnitary X.T X.cg X.chr)
      (fun a π ha hc hr w => rankTwo hP.what₂.fin hP.what₂.temp hP.what₂.clo X.T X.cg a π ha hc hr w)
  exact ⟨htie0, ha5, ha7, tieLab_of_lab X.T X.lab, heckeSplitOne_of_side X.chr, cancel_of_tie X.T,
    fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩

end GlobalTheory.ParLawsBare

end
