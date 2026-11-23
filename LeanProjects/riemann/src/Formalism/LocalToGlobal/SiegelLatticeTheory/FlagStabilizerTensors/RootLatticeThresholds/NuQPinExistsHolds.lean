import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsSumCPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdCellOffCHoldsOfVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Gam1TieCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiniteLevelVolumeOfMeasure
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NGLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataKppVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

theorem massDataY_tt {D : D7} (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) :
    (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).tt = PgC T.Y := by
  have h1 := Formalism.L2.SG.MassDataConc.ttC_of_split T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u') sd C Th vR Q
    T.Y.M T.Y.δ i0 i0' νq (Formalism.L2.SG.Pf.gSplitX_holds T.X)
  unfold Formalism.L2.SG.MassDataConc.ttC at h1
  rw [h1, PgC, Formalism.L2.SG.Pf.tt_eq_holds T.X T.Y.TR]
  have hS := Formalism.L2.SG.Pf.gSplitX_holds T.X
  have e : ∀ p : Formalism.L2.SG.TypedSets.TypX T.X,
      (1 + 3 / ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ)) = (fun q : ℕ => 1 + 3 / (q : ℝ)) (Formalism.L2.SG.TypedSets.gOf p) := by
    intro p
    rw [(hS p).1]
    rfl
  rw [Finset.prod_congr rfl fun p _ => e p]
  have hq : ∀ p : Formalism.L2.SG.TypedSets.TypX T.X,
      Formalism.L2.SG.TypedSets.gOf p = D.host.g 0 ∨ Formalism.L2.SG.TypedSets.gOf p = D.host.g 1 := by
    intro p; unfold Formalism.L2.SG.TypedSets.gOf; split_ifs <;> simp
  have h2 := Formalism.L2.SG.Pf.SatGram.prod_two (M := ℝ) (fun p : Formalism.L2.SG.TypedSets.TypX T.X => Formalism.L2.SG.TypedSets.gOf p)
    (D.host.g 0) (D.host.g 1) D.host.g_ne hq (fun q : ℕ => 1 + 3 / (q : ℝ))
  refine h2.trans ?_
  rw [Formalism.L2.SG.Pf.SatGram.card_typ (Formalism.L2.SG.Pf.SatGram.gCount_of Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds) 0,
    Formalism.L2.SG.Pf.SatGram.card_typ (Formalism.L2.SG.Pf.SatGram.gCount_of Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds) 1]

theorem idZero_tO {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (hne : u ≠ u')
    (hWD : Formalism.L2.SG.WuDecay.WuDecay X) : (Y.tO u u').IdZero := by
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hO := Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := Y) hWD u u'
  have hI := Formalism.L2.SG.Pf.idCellOffC_holds_of_vol Formalism.L2.SG.Closed.VolPosC_holds D X Y u u' hF hO hne
  have hc : Continuous (Formalism.L2.SG.PackageTie.hsEmb (Wq := Formalism.L2.SG.TermOp.CM (Y.cs u'))
      (Wp := Formalism.L2.SG.TermOp.CM (Y.cs u))) := LinearMap.continuous_of_finiteDimensional _
  have h2 := hI.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := Formalism.L2.SG.TermOp.CM (Y.cs u'))
      (Wp := Formalism.L2.SG.TermOp.CM (Y.cs u))).toAddMonoidHom hc
  simp only [LinearMap.toAddMonoidHom_coe, map_zero] at h2
  unfold Formalism.FourierDecayAlt.PB.Terms.IdZero Formalism.FourierDecayAlt.PB.Terms.part
  rw [← tsum_subtype]
  exact h2.tsum_eq

theorem splitAll_holds : SplitAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hg3
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : (T.Y.tO u u').AbsConv :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  have hq : ∀ v, 3 ≤ Fintype.card (T.Y.TR.Fq v) := fun v => by
    rcases T.Y.TR.card_q v with h | h <;> rw [h] <;> exact hg3 _
  rw [massDataY_tt]
  exact ⟨hAbs, Formalism.L2.SG.RowsConc.normExpSatTied_holds D T.X T.Y u u' hCT,
    Formalism.L2.SG.TermOp.ggBound T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u')
      Formalism.L2.SG.Closed.TermsGGBound_holds T.Y.psi_ne hq,
    Formalism.L2.SG.TermOp.rowOrth T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u'),
    Formalism.L2.SG.Pf.SatGram.corankPos_tO T.Y u u', idZero_tO T.Y u u' hne hWD,
    Formalism.L2.SG.TermOp.GG_diag T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u')⟩

section Link

def KppVolAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y →
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 →
    Formalism.L2.SG.TypedSets.KppVolAt T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0
      (Formalism.L2.SG.LocVol.locOf T.X u u' T.ψ) (Formalism.L2.SG.NGAnalytic.MassDataLemmas.canonicalAnalyticData T.X T.Y u u' T.ψ)

theorem exists_typ {D : D7} (X : HidaSetting D) :
    ∃ typ : Formalism.L2.SG.TypedSets.TypX X ≃ Bool × InfinitePlace D.host.E, ∀ p,
      (Formalism.L2.SG.TypedSets.gOf p : ℝ) = if (typ p).1 then (D.host.g 0 : ℝ) else (D.host.g 1 : ℝ) := by
  classical
  set q : Formalism.L2.SG.TypedSets.TypX X → Prop := fun p => Formalism.L2.SG.TypedSets.gOf p = D.host.g 0 with hq
  have hcE : Fintype.card (InfinitePlace D.host.E) = D.R.f := Formalism.MainNotions.InterlacingSignCuts.card_places D
  have hc : ∀ i : Fin 2, Fintype.card {p : Formalism.L2.SG.TypedSets.TypX X // Formalism.L2.SG.TypedSets.gOf p = D.host.g i} = D.R.f := by
    intro i
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Formalism.L2.SG.Pf.DstarIdxPf.typEquiv X i),
      Formalism.L2.SG.Pf.DstarIdxPf.card_over X i]
  have hneg : ∀ p : Formalism.L2.SG.TypedSets.TypX X, ¬ q p ↔ Formalism.L2.SG.TypedSets.gOf p = D.host.g 1 := by
    intro p
    simp only [hq]
    constructor
    · intro h; unfold Formalism.L2.SG.TypedSets.gOf at h ⊢; split_ifs at h ⊢ <;> simp_all
    · intro h e; exact D.host.g_ne (e.symm.trans h)
  have e0 : {p // q p} ≃ InfinitePlace D.host.E := Fintype.equivOfCardEq (by rw [hc 0, hcE])
  have e1 : {p // ¬ q p} ≃ InfinitePlace D.host.E :=
    Fintype.equivOfCardEq (by rw [Fintype.card_congr (Equiv.subtypeEquivRight hneg), hc 1, hcE])
  let typ : Formalism.L2.SG.TypedSets.TypX X ≃ Bool × InfinitePlace D.host.E :=
    (Equiv.sumCompl q).symm.trans ((Equiv.sumComm _ _).trans ((Equiv.sumCongr e1 e0).trans
      (Equiv.boolProdEquivSum (InfinitePlace D.host.E)).symm))
  refine ⟨typ, fun p => ?_⟩
  by_cases h : q p
  · have : (typ p).1 = true := by
      simp [typ, Equiv.sumCompl_symm_apply_of_pos h, Equiv.boolProdEquivSum]
    rw [this, if_pos rfl]
    exact_mod_cast h
  · have : (typ p).1 = false := by
      simp [typ, Equiv.sumCompl_symm_apply_of_neg h, Equiv.boolProdEquivSum]
    rw [this, if_neg (by simp)]
    exact_mod_cast (hneg p).1 h

theorem linkAll_of (hKpp : KppVolAll) : LinkAll := by
  intro D T u u' e τ X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hdet hDst
  have hH : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, Formalism.L2.SG.Closed.level_subgroup_properties T.X, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  have hG := Formalism.L2.SG.IntegralApproximation.Gam1TieC_holds T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq T.Y
  have hD := Formalism.L2.SG.IntegralApproximation.MassDataDstarX_holds T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq
    (Formalism.L2.SG.LocVol.locOf T.X u u' T.ψ) (Formalism.L2.SG.NGAnalytic.MassDataLemmas.canonicalAnalyticData T.X T.Y u u' T.ψ) hH
    (hKpp D T u u' X0 hne hSt hCT hdet)
  obtain ⟨typ, htyp⟩ := exists_typ T.X
  refine ⟨hG, Formalism.L2.SG.MassDataConc.pairSum_eq _ hG, ⟨typ, htyp⟩, hCT.2.2.1 u, hCT.2.2.1 u', ?_⟩
  rw [hDst]
  exact hD.trans hCT.2.2.2.1

end Link

section Choices

open ValuativeRel

def NuQPinExists : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word), u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' →
    ∃ νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf, NuQPin T.X u u' νq

def LocSpExists : Prop := ∀ (D : D7) (T : STies D), Nonempty (LocSp D T.Y.M)

theorem choicesC_of (hNu : NuQPinExists) (hL : LocSpExists) : ChoicesC := by
  intro D T u u' hne hSt _ hk
  obtain ⟨νq, hνq⟩ := hNu D T u u' hne hSt
  obtain ⟨X0, hX0⟩ := Formalism.L2.SG.NGLeaves.nondegenerate_gram_tuple D T.X
  obtain ⟨Lsp⟩ := hL D T
  have hϖ : ∀ p : PlF D, ∃ x : 𝒪[(D.s.atP p).Fp], Irreducible x := fun p => by
    haveI := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ' using hϖ
  obtain ⟨κ, hκ⟩ := Formalism.L2.SG.DataCut.rowLabelExists_holds D u u' (T.X.Fu u) (T.Y.what₂ u) (T.Y.rowsOK u)
  let i0 : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k := fun _ => ⟨0, by omega⟩
  exact ⟨i0, i0, νq, X0, Lsp, ϖ, κ, Formalism.L2.SG.NGAnalytic.MassDataLemmas.pairSys0 u u' (T.X.Fu u) (T.Y.what₂ u),
    fun _ => rfl, Formalism.L2.SG.RealObj.InfCut.real_point_representative_exists D T.X u u' 1 one_pos i0, hνq, hX0, hϖ', hκ⟩

end Choices

section Leaves

theorem kppVolAll_holds : KppVolAll :=
  fun _ T u u' X0 _ _ _ _ => kpp_volume_at_instance T.X T.hb T.Y.hK _ _ u u' X0 _ _

theorem linkAll_holds : LinkAll := linkAll_of kppVolAll_holds

theorem nuQPinExists_holds : NuQPinExists := by
  intro D T u u' _ _
  have hP : Formalism.L2.SG.NGPin.PinHaarEx := Formalism.L2.SG.NGPin.pinHaarEx_of_place
    (Formalism.L2.SG.RootPatterns.placeHaar_of_loc Formalism.L2.SG.NGPin.locRootHaar_holds)
  exact ⟨fun γ => (Formalism.L2.SG.NGPin.exists_at T.X u u' hP γ).choose,
    fun γ h => (Formalism.L2.SG.NGPin.exists_at T.X u u' hP γ).choose_spec.1 h,
    fun w hw => (Formalism.L2.SG.NGPin.exists_at T.X u u' hP (gamW T.X u u' w)).choose_spec.2.2 w hw rfl⟩

theorem locSpExists_holds : LocSpExists := fun D T =>
  ⟨{ V := Formalism.L2.SG.TermLoc.Vp D
     H := fun p => Formalism.L2.SG.TermLoc.locHerm T.Y.M p (T.Y.agree p).2.2.1
     rank := Formalism.L2.SG.TermLoc.finrank_Vp
     bc := Formalism.L2.SG.TermLoc.baseChange₂ D
     bc_smul := Formalism.L2.SG.TermLoc.baseChange_smul₂
     bc_span := Formalism.L2.SG.TermLoc.span_baseChange_eq_top
     bc_form := fun p x y => Formalism.L2.SG.TermLoc.baseChangeAt_form T.Y.M p (T.Y.agree p).2.2.1 x y }⟩

theorem choicesC_holds : ChoicesC := choicesC_of nuQPinExists_holds locSpExists_holds

end Leaves

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
