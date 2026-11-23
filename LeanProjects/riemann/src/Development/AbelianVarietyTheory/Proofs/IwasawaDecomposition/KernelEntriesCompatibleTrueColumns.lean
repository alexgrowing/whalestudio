import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
import Formalism.LocalToGlobal.Columns.ChainTopTilQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open Formalism.HermitianLatticesTheory

theorem topChain : TopChain := by
  classical
  intro D X u C r Pr Ch sel S mu cst L σ v m2 hX hPr hc hm hpi h
  obtain ⟨hSS, hlev, pt, ix, yb, pT, hN, hyb, hE, hC, ⟨hTN, hTX⟩, hpin, hpin'⟩ := h
  have key : ∀ (c' : C.cls (m2 + 1 + 1)) d, OverRow sel mu v d (pT c') →
      HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N ∧ ∀ c, HEq (r.Xi (m2 + 1) c c') fun x => σ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x) := by
    intro c' d hd
    obtain ⟨p', hp, hrow⟩ := hd
    have gen : ∀ (j : ℕ) (hj : j = m2 + 1 + 1) (q : DecoF X.E (D.R.N j) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))), HEq (pT c') q →
        HEq (pT c').deco.1.N q.deco.1.N ∧ ∀ c, HEq (fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x))
          (fun x => σ (XiTopG Ch sel mu cst (m2 + 1) j (D.R.N j) (pt (m2 + 1) le_rfl c) (yb c) q x)) := by
      intro j hj q hq
      subst hj
      obtain rfl := eq_of_heq hq
      exact ⟨HEq.rfl, fun _ => HEq.rfl⟩
    obtain ⟨g1, g2⟩ := gen D.R.m (by omega) p' hp
    refine ⟨?_, fun c => ?_⟩
    · rw [hTN c']
      refine g1.trans (heq_of_eq ?_)
      rw [hrow.1]
      rfl
    · have e : r.Xi (m2 + 1) c c' = fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x) := funext (hTX c c')
      rw [e]
      refine (g2 c).trans (heq_of_eq ?_)
      rw [xiTopTilQ_holds Ch sel mu cst hX hPr hc hm v hpi _ _ d p' hrow.1 hrow.2 (hyb c)]
  refine ⟨hSS, hlev, pt, ix, yb, fun c' => if h : ∃ d, OverRow sel mu v d (pT c') then some h.choose else none,
    hN, hyb, hE, hC, fun c' d hd => ?_, fun c c' d hd => ?_, hpin, fun c' => ?_⟩
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).1
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).2 c
  · rw [hpin' c']
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨_, dif_pos ⟨d, hd⟩⟩
    · rintro ⟨d, hd⟩
      dsimp only at hd
      split_ifs at hd with h
      exact h

section Gen
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xiOver_eq_topG {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl
end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def kerRd (u : B.Word) (a : I.ι) : KerRead ((I.rec7 l Z).chTw u a) B.fields where
  SS := Sall (Pr := B.primes X) I.sel (I.tup a) u
  lev := levC (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  N i c := ((I.stp u a i).rep c).1.1.deco.1.N
  Xi i c c' x := B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)
  pin i c := i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1

theorem kerRd_top {m2 : ℕ} (hm : B.R.m = m2 + 2) (u : B.Word) (a : I.ι) :
    (I.kerRd l Z u a).IsChainTop I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) B.embLL u m2 := by
  have hm' : (I.rec7 l Z).R.m = m2 + 2 := hm
  refine ⟨rfl, rfl, fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => Idx.get c.1 (by omega),
    fun c => ((I.stp u a (m2 + 1)).rep c).1.2, fun c => ((I.stp u a (m2 + 1 + 1)).rep c).1.1, fun _ _ _ => rfl,
    fun c => PtAt.mem_ybSet _ (by omega), fun i hi c c' x => ?_, fun c c' x => ?_, ⟨fun _ => rfl, fun c c' x => ?_⟩, fun i hi c => show i + 1 ≤ B.R.m ∨ _ from Or.inl (by omega), fun c' => ?_⟩
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u m2 c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (m2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega : m2 + 1 + 1 = B.R.m), xiOver_eq_topG]
    rfl
  · exact or_iff_right (by show ¬ m2 + 1 + 1 + 1 ≤ B.R.m; omega)

theorem mem_stdL_iff {R : Ranks} (H : Host R) (n : ℕ) (x : Fin n → H.E) : x ∈ Th.stdL H n ↔ ∀ k, IsIntegral ℤ (x k) := by
  refine ⟨fun h k => ?_, fun h k _ => Submodule.mem_one.2 ⟨⟨x k, h k⟩, rfl⟩⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h k trivial)
  rw [← hr]
  exact NumberField.RingOfIntegers.isIntegral_coe r

theorem chiRec_lat (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) =
      I.chi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) := by
  have h1 := (O u a).dt_lat i c
  have h2 := hidl.2.2.2.2 _ ((O u a).L0 i) ((O u a).lat i c)
  rw [← h1] at h2
  have e0 : ((O u a).L0 i).1 = Th.stdL B.host (B.R.N i) := by
    ext x
    rw [(O u a).lattice_integral_coordinates]
    exact (mem_stdL_iff B.host _ x).symm
  have e1 : ((O u a).lat i c).1 = ((I.stp u a i).rep c).1.1.deco.1.N := hO.lat u a i c
  rw [e0, e1] at h2
  have h3 : Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N = idl (QuotientGroup.mk ((O u a).dt i c)) := h2.symm
  rw [h3, TaylorLogMetric.chiRec_idl _ _ hidl.1, ← h3]
  have h4 : ((TaylorLogMetric.chiQ (I.rec7 l Z) (QuotientGroup.mk ((O u a).dt i c)) : ℂˣ) : ℂ) = ((tildeQ B.host I.SQ I.C.chiPsi (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ) := by
    rw [hO.dt u a i c]
    rfl
  rw [h4]
  exact GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1

theorem kerRd_Th (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (TaylorLogMetric.chiRec (I.rec7 l Z) idl) I.J.cD) i c c' =
      I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := by
  refine (congrArg (fun A => (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) A i c c')
    (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).symm).trans ?_
  have he : (I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N =
      I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N := by
    funext z
    show Th.chiFac B.host _ _ _ _ _ * _ = Th.chiFac B.host _ _ _ _ _ * _
    unfold Th.chiFac
    rw [I.chiRec_lat l Z hok hidl hO u a i c, I.chiRec_lat l Z hok hidl hO u a (i + 1) c']
  show thC _ _ _ _ _ _ _ _ _ _ ((I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) = thC _ _ _ _ _ _ _ _ _ _ (I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N)
  rw [he]
  rfl

theorem kerEntTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex O E hQ hO hU hE hS
  obtain ⟨idl, hidl⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  obtain ⟨⟨kf, hkf⟩, hAd⟩ := hE
  have hm := hok.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hok.sel_ok u ⟨hok.T_mem u, hok.g_mem⟩).2.1
  let t : KerEntTied ex :=
    { cc := ⊤
      cc_rec := B.toPre.ccK_top.symm
      cc_ok := ⟨top_ne_bot, by simp⟩
      δ := I.J.δ
      δ_ok := hok.amb_ok.delta
      B := I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      χ := TaylorLogMetric.chiRec (I.rec7 l Z) idl
      χ_ok := TaylorLogMetric.isChi_chiRec _ _ hidl
      idl := idl
      idl_ok := hidl
      χ_rec := rfl
      cD := I.J.cD
      X := B.fields
      seam := seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      seam_ok := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      Pr := B.primes X
      pr_ok := l.pr
      g_rec := fun i => rfl
      Ch := I.Ch
      sel := I.sel
      S := I.S
      word := fun u => u
      T_rec := fun u => rfl
      tup := I.tup
      Q_rec := hQ
      cst := I.cst
      idx := I.idx
      m2 := B.R.m - 2
      glob := I.glob
      glob_σ := rfl
      glob_xi := rfl
      idx_ok := hok.idx_ok
      O := O
      rd := I.kerRd l Z
      rd_chain := fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hok.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a)
      O_dgen := hO.dgen
      O_S := hO.S
      O_lat := fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
      O_Th := fun u a i c c' => (hO.Th u a i c c').trans (I.kerRd_Th l Z hok hidl hO u a i c c').symm
      unf := fun u a i hi => (hU u a i hi).unfIs _
      ent := E
      ent_lam := fun u w h => (hS u w h).1
      kf := kf
      kf_un := hkf
      served := hS }
  exact ⟨t, ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl,
    heq_of_eq (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J _).symm, rfl, hO⟩, rfl, hAd, fun u a => I.kerRd_top l Z hm u a⟩

end GlobalTheory.Mem.Col2.TC
end
