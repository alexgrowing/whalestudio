import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KeepsPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.OffTrace
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise
end GlobalTheory.OffTrace
open GlobalTheory.LatPair GlobalTheory.FinPl in
open scoped Pointwise in
theorem GlobalTheory.OffTrace.embA_moves_off_level_iff_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (GlobalTheory.FinPl.Moves (Yc (I.rec7 l Z) 0) (embA a.d.B.d a.d.B.o κ) (a.v.N 0) (a.v.N 0) (fun p => p ∉ a.v.gP) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∉ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  have h0 : 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := by
    have := Formalism.BasicNotions.Ranks.rS_two (I.rec7 l Z).R; omega
  have hB := ha.bot.1 h0
  have key : ∀ B' : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, B' = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0 →
      HEq (embA B'.d B'.o) (embA ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o) := by
    rintro _ rfl; rfl
  have hE := eq_of_heq (key a.d.B.lev hB)
  have hE' : embA a.d.B.d a.d.B.o κ = ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1)) :=
    DFunLike.congr_fun hE κ
  rw [hE']
  have hm : 0 < (I.rec7 l Z).R.m := by omega
  have hN : Submodule.IsLattice (I.rec7 l Z).host.E (a.v.N 0) := (ha.vis.sd 0 hm).1
  have hL : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x 0).L := (ha.x 0 (Nat.zero_le _)).sd.1
  rw [GlobalTheory.T.carriesLatticeCompletion_iff_forall_place _ _ _ hN, GlobalTheory.T.carriesLatticeCompletion_iff_forall_place _ _ _ hL]
  have hA : ∀ v, Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).V 0)
      (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0) (· = v) ↔
      Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).V₀ (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1)) (a.o.M 0 _ h0)
        (a.o.M 0 _ h0) (· = v) := fun v =>
    GlobalTheory.OffTrace.carriesLattice_wittEmbedding_iff_core _ _ _ v ((ha.shape.good v).bf 0 _ h0).monoV _
  have hoff : ∀ v, v ∉ a.v.tP → (Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).V 0)
      (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0) (· = v) ↔
      Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = v)) := by
    intro v hv
    obtain ⟨LL, -, hO⟩ := (ha.shape.split v hv).core 0 _ h0
    exact (hA v).trans (GlobalTheory.OffTrace.moves_emb_iff _ _ _ _ v hO κ)
  have hcore : ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X 0).rank) a.k),
      (mt ((I.rec7 l Z).sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
      (Moves ((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).V 0)
        (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).d.emb0 (((commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0)
        (· = (a.o.p i).v) ↔ g • a.o.Q 0 i = a.o.Q 0 i) := by
    intro i g hg
    have hgl := ha.shape.glued 0 _ h0 i
    exact (hA _).trans ((GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff (a.o.β₀ 0 _ h0 i) (a.o.M 0 _ h0) _
      ((ha.shape.good (a.o.p i).v).bf 0 _ h0).sdV₀ hgl.lat _ _
      (GlobalTheory.T.splitPlace_besselCore_matrix_eq_blockDiagonal_one _ _ _ hgl.sum κ g hg)).trans (GlobalTheory.OffTrace.glued_stab_iff _ _ _))
  have hX : ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X 0).rank) a.k),
      (mt ((I.rec7 l Z).sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
      (Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = (a.o.p i).v) ↔ g • (a.o.Q 0 i).lat = (a.o.Q 0 i).lat) :=
    fun i g hg => GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff (a.o.β 0 i) (a.g.x 0).L _ (ha.x 0 (Nat.zero_le _)).sd
      (ha.shape.pre.latT 0 (Nat.zero_le _) i) κ g hg
  have hTg : ∀ i, (a.o.p i).v ∉ a.v.gP := fun i hg' =>
    Finset.disjoint_left.1 ha.vis.disj hg' ((ha.shape.pre.tP _).2 ⟨i, rfl⟩)
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun i g hg => (hcore i g hg).1 (h _ (hTg i))⟩
    by_cases hT : v ∈ a.v.tP
    · obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 hT
      obtain ⟨g, hg⟩ := GlobalTheory.OffTrace.exists_gl_frame (a.o.β 0 i) κ
      have h1 := (hcore i g hg).1 (h _ hv)
      exact (hX i g hg).2 (by rw [← Pair.smul_lat, h1])
    · exact (hoff v hT).1 (h v hv)
  · rintro ⟨h1, h2⟩ v hv
    by_cases hT : v ∈ a.v.tP
    · obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 hT
      obtain ⟨g, hg⟩ := GlobalTheory.OffTrace.exists_gl_frame (a.o.β 0 i) κ
      exact (hcore i g hg).2 (h2 i g hg)
    · exact (hoff v hT).2 (h1 v hv)
end
