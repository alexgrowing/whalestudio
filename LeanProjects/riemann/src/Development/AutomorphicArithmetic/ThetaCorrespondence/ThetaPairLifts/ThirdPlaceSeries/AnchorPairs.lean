import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorCentralTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatchStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem anchor_pairs_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hPu z hzf hzc v hv u
  obtain ⟨-, hInf, -, hMatch, -, -⟩ := _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt W hB
  have hEv := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
    (z * (show GA D (D.sp.Y 0) from W.Q.tS)) v (by simp) hInf hB.gap hB.idE (hMatch z hzf hzc) hv
  obtain ⟨⟨j, hjbij, hj⟩, -⟩ := hEv
  have hF := hB.fin
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  have hpair : ∀ (Tm : MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)) (C : Cu W.S.X u W.S.Y.hK),
      _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) C
        ⟪((j Tm : HHX W.S.X) : L2X W.S.X), PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C⟫_ℂ := by
    intro Tm C
    unfold _root_.GlobalTheory.MiTop.IsPairing'
    let g : L2X W.S.X := ((j Tm : HHX W.S.X) : L2X W.S.X)
    have hg : (g : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] fun x => star (evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) x) := hj Tm
    refine ⟨star g, ?_, ?_⟩
    · have h1 : ((star g : L2X W.S.X) : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] star (g : W.S.X.B.I.GA → ℂ) := MeasureTheory.Lp.coeFn_star g
      refine h1.trans ((hg.fun_comp star).trans (Filter.EventuallyEq.of_eq ?_))
      funext x
      exact star_star _
    · rw [star_star]
  refine ⟨fun φ => ?_, fun T hT C => ⟨_, hpair ⟨T, hT⟩ C⟩, ?_⟩
  · obtain ⟨C, hC⟩ := (W.S.bij u).2 (D.eMu u φ).1 (hram (D.eMu u φ).2)
    exact ⟨C, hC⟩
  · obtain ⟨φr, hφr⟩ := hPu u
    let x := (D.s_Cu u).symm ⟨φr.1, φr.2.1⟩
    let C : Cu W.S.X u W.S.Y.hK := (W.S.hI hF).eCu u x
    have hpin := W.S.colPin hF u x
    have hC : _root_.GlobalTheory.MiTop.IsColumnForm W u C ((D.eMu u).symm φr) := by
      show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK C = _
      rw [LinearEquiv.apply_symm_apply, ← Formalism.L2.SG.ColDict.colDict_apply W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)]
      have hpin' : Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u) C = D.s_Cu u x := hpin
      rw [hpin', LinearEquiv.apply_symm_apply]
    let P : HHX W.S.X := (Formalism.L2.SG.PackageTie2.sOf hF).Pu u C
    have hP : P ≠ 0 := by
      have e := (W.S.hI hF).Pu_eq u x
      intro h0
      apply hφr
      have : (W.S.hI hF).eHH (D.s.Pu u x) = 0 := e.trans h0
      exact (LinearIsometryEquiv.map_eq_zero_iff _).1 this
    obtain ⟨Tm, hTm⟩ := hjbij.2 P
    refine ⟨(D.eMu u).symm φr, C, _, Tm.1, Tm.2, hC, hpair Tm C, ?_⟩
    rw [hTm]
    have hPv : ((P : HHX W.S.X) : L2X W.S.X) = PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C := rfl
    rw [hPv]
    refine inner_self_ne_zero.2 ?_
    rw [← hPv]
    exact fun h => hP (Subtype.ext h)
end GlobalTheory.MiTop
end
