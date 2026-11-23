import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvGLawOfFixedCol
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeLevelLastStepSymmetricRowsEqTwistLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTopStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pdv

theorem stabStd_eq_stabSet {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun γ => (fun v => γ.1 v) '' ((I.stp u a i).rep c).1.2 = ((I.stp u a i).rep c).1.2) := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hs : _ = _ := s.2
    refine ⟨s.1, congrArg (fun p => p.1.1) hs, congrArg (fun p => p.1.2) hs, ?_⟩
    refine Prod.ext ?_ rfl
    exact GlobalTheory.KerJ.ufGL_val s.1.1
  · rintro ⟨b, hb, hq, rfl⟩
    refine ⟨⟨b, Subtype.ext (Prod.ext hb hq)⟩, ?_⟩
    refine Prod.ext ?_ rfl
    exact (GlobalTheory.KerJ.ufGL_val b.1).symm

theorem rep_coset_empty {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m)
    (c : (I.stp u a i).Cl) : ((I.stp u a i).rep c).1.2 = ∅ := by
  have key : ∀ y : Ys B.fields (B.R.N i), y = Ys.triv _ _ → ∀ s N, s ∈ y.ys N → s = ∅ := by
    rintro y rfl s N hs
    exact hs
  exact key _ (by unfold ysAt; exact if_neg hi) _ _ ((I.stp u a i).rep c).2

theorem stabStd_eq_stabSet_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≠ B.R.m) (c : ((I.rec7 l Z).chTw u a).cls i) :
    stabStd I l Z u a i c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
      ((I.stp u a i).rep c).1.1 (fun _ => True) := by
  rw [stabStd_eq_stabSet, rep_coset_empty I u a i hi c]
  congr 1
  funext γ
  simp

theorem stab_pin : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → ∀ u a, GlobalTheory.KerJ.StabPin t u a (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I hI hP l Z L hT Gi Gl K Y cX ex t hN hK hR u a
  change B.Word at u
  change I.ι at a
  obtain ⟨cc, cc_rec, cc_ok, δ', δ_ok, B', χ, χ_ok, idl, idl_ok, χ_rec, cD, X', seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S', word,
    T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf,
    kf_un, served⟩ := t
  obtain ⟨hX, hseam, hPr, hCh, hsel, hS, hword, htup, hcst, hidx, hm2, -, -, -, -⟩ := hK
  subst hX
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hCh
  obtain rfl := eq_of_heq hsel
  subst hS
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hidx
  subst hm2
  obtain ⟨r, hr, hrs⟩ := hR u a
  obtain rfl := eq_of_heq hr
  unfold GlobalTheory.KerJ.StabPin
  dsimp only
  have hm : B.R.m = B.R.m - 2 + 2 := (hI.idx_ok a).hm
  have h1 : B.R.m - 2 + 1 + 1 = B.R.m := by omega
  obtain ⟨hXo, hPro, -⟩ := base_fields_primes_ok B X
  have hG : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get h) := by
    intro j b h
    unfold levGAt
    rw [← Idx.some_get b h]
    rfl
  have hQ : ∀ j (b : Idx I.sel (I.tup a) (I.idx a) j) (h : j < B.R.m),
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levQ j (b.get h) := by
    intro j b h
    unfold levQAt
    rw [← Idx.some_get b h]
    rfl
  have hGt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twLt I.Ch B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levGAt
    rw [hb]
    exact (topLev_levG_m _ _ _ _ _).trans (GlobalTheory.T.typePrimeLevel_lastStep_symmetricRows_eq_twistLevel B.fields (B.primes X) B.R I.Ch hXo hPro hI.ch_ok)
  have hQt : ∀ b : Idx I.sel (I.tup a) (I.idx a) B.R.m,
      levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m b = twTt (R := B.R) I.sel (I.tup a) B.R.m := by
    intro b
    have hb : b.1 = none := Option.not_isSome_iff_eq_none.1 fun h => lt_irrefl _ (b.2.1 h)
    unfold levQAt
    rw [hb]
    refine (topLev_levQ_m _ _ _ _ _).trans ?_
    have hd : topDep B.R (I.cst a).M = 4 * B.R.m := by
      have := (hN a).2.1
      unfold topDep
      exact max_eq_left (by omega)
    rw [hd]
    exact GlobalTheory.T.level_quotient_eq_twisted_top B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) hXo hPro hI.sel_ok (fun i => hI.g_mem i)
      (fun v => hI.T_mem v)
  have hTop : ∀ j (hj : j = B.R.m) (c : ((I.rec7 l Z).chTw u a).cls j),
      stabStd I l Z u a j c = GlobalTheory.KerJ.stabSet (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (twLt I.Ch j)
        (twTt (R := B.R) I.sel (I.tup a) j) ((I.stp u a j).rep c).1.1 (fun _ => True) := by
    intro j hj c
    subst hj
    rw [stabStd_eq_stabSet_triv I l Z u a _ (by omega) c, hGt, hQt]
  refine ⟨fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => c.1.get (by omega),
    fun c => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2, fun c => ((I.stp u a (B.R.m - 2 + 1 + 1)).rep c).1.1,
    fun i _ c => hrs.1 i c, fun c => PtAt.mem_ybSet _ h1, ?_, ?_, ⟨fun c' => hrs.1 _ c', ?_⟩, ?_, ?_, fun c => hTop _ h1 c⟩
  · intro i hi c c' x
    rw [hrs.2 i (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm
      (Idx.some_get c'.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get c.1 (by omega)).symm]
    rfl
  · intro c c' x
    rw [hrs.2 _ (by omega) c c' x]
    show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) h1,
      GlobalTheory.T.lastColumnStepDatum_eq_twistTopDatum B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) u (B.R.m - 2) h1]
    rfl
  · intro i _ hi c
    rw [stabStd_eq_stabSet_triv I l Z u a i (by omega) c, hG i c.1 (by omega), hQ i c.1 (by omega)]
    rfl
  · intro b c
    obtain ⟨b0, hb0⟩ := (hI.idx_ok a).last_uniq
    have hcb : c.1.get (by omega) = b := (hb0 _).trans (hb0 b).symm
    rw [stabStd_eq_stabSet, hG _ c.1 (by omega), hQ _ c.1 (by omega), hcb]
    rfl

end GlobalTheory.Pdv

end
