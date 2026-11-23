import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamTrace.Rows
open GlobalTheory.FinPl
section Gen
variable {D : D7}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Gen
section Loc
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem mem_rJ_iff_finE_mem_St_and_block_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (y : GA D (Yc D 0)) (hy : y ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from y) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ finE (Yc D 0) y ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ∧
      (fun PP : (_root_.GlobalTheory.Fam.pk_z W).Pg => upperLeftBlock (r_le_Y 0) (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (Yc D 0) y))) ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := by
  have hn : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  have key := (GlobalTheory.LevYZero.lev_datY_zero (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) _ D.R.r D.R.t (r_le_Y 0) hn (_root_.GlobalTheory.Fam.pk_z W).Pg (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi
    (fun _ => 1) rfl (finE (Yc D 0) y) (GlobalTheory.LevSplit.finE_mem_UA _ y)).1
  exact Iff.trans ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩ key
set_option maxHeartbeats 1000000 in
theorem main_alt_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (u : D.what₂.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (ha : a.Is)
    (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t)))
    (x : GA D (Yc D 0)) (hx : x ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from (a.g.b 0)⁻¹ * x * a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ _root_.GlobalTheory.FamTrace.InLevelGroupOfY a x := by
  obtain ⟨hV, hG⟩ := ha.tie row col
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hb : a.g.b 0 ∈ GfC (Yc D 0) := by
    have h1 := ha.vis.b 0
    rw [hV.b 0] at h1
    exact h1
  have hsd := hW.bot.hyp.2.2.2.1.lev.βY 0 hm
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hsd
  obtain ⟨c, hβ, -⟩ := hsd
  have hoff := GlobalTheory.StMoves.moves_conj_iff x (hV.moves 0 hm (fun p => p ∉ a.v.gP) fun _ h => h)
  choose e he hM using fun i => hG.frame i 0 ((a.G i).s + 1) (Nat.zero_add _)
  have hex : ∀ i, ∃ m, (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m := fun i =>
    ⟨_, (eq_coordHom_iff _ (a.G i).q.pr _ _ ((a.G i).FY 0 _ (Nat.zero_add _)).βγ ((a.G i).FY 0 _ (Nat.zero_add _)).γβ x _).2 rfl⟩
  have hloc := fun i m (hmat : (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m) hst =>
    red_iff (a.G i).q (hG.idem i).1 (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (a.g.b 0) x (a.G i).hs (a.G i).S _ (e i) (he i) (hM i) (r_le_Y 0) m hmat hst
  rw [_root_.GlobalTheory.FamTrace.Rows.mem_rJ_iff_finE_mem_St_and_block_mem W _ (mul_mem (mul_mem (inv_mem hb) hx) hb), (hG.lev _).1]
  constructor
  · rintro ⟨hst, hred⟩
    refine ⟨hoff.1 (moves_mono (fun _ _ => trivial) ((movesLocal D _ _ hΛ _).2 ((st_iff _ _ _ hβ hΛ _).1 hst))), ?_⟩
    exact fun i m hmat => (hloc i m hmat hst).1 (hred i)
  · rintro ⟨h1, h2⟩
    have hst : finE (Yc D 0) ((a.g.b 0)⁻¹ * x * a.g.b 0) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY 0) := by
      refine (st_iff _ _ _ hβ hΛ _).2 fun v => ?_
      by_cases hv : v ∈ a.v.gP
      · obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
        obtain ⟨m, hmat⟩ := hex i
        have hR : ((a.G i).S.T (Fin D.R.t)).Regular := GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
        exact moves_of_stab (a.G i).q (hG.idem i).1 (Yc D 0) _ _ hβ hΛ (a.g.b 0) x _ _
          ((e i).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) (hM i) m hmat
          ((hR.2.2 0 _ (Nat.zero_add _)).2.2 (h2 i m hmat))
      · exact moves_mono (fun p hp => by rw [hp]; exact hv) (hoff.2 h1)
    refine ⟨hst, fun i => ?_⟩
    obtain ⟨m, hmat⟩ := hex i
    exact (hloc i m hmat hst).2 (h2 i m hmat)
end Real
end GlobalTheory.FamTrace.Rows
theorem GlobalTheory.FamTrace.conj_mem_rows_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ x ∈ GfC ((I.rec7 l Z).sp.Y 0), ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * x * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ _root_.GlobalTheory.FamTrace.InLevelGroupOfY a x) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ x hx
  exact _root_.GlobalTheory.FamTrace.Rows.main_alt_alt W hA.pk u a ha row col x hx
end
end
