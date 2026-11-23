import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.SelC
section Gen
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)
end Gen
section Main
variable {B : Base} {X : PreX B.toPre} {I : TC B X}
variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}
def squareIntegrableColumnsOfKernel (hOk : (famC I hX U Xg tr).fam3.Ok3 1) (T : _root_.Formalism.L2.TiedDataSKAlt ex) (hS : I.StdKer l Z T.ker)
    (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs))
    (R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp)
    (htup : R.I.tup = ixOf I U) (hw : ∀ u, R.I.wU u = u) : _root_.Formalism.L2.DIV.SquareIntegrableColumns T R.extendedDatum where
  X := B.fields
  e := B.tauLL
  c := colRecK h hp l Z ht hJ hX U Xg tr T.ker
  Sp := Sp
  colTie := ⟨rfl, HEq.rfl⟩
  kerTie := by
    obtain ⟨h1, h2, h3⟩ := tup_heq ht U T.ker.X hS.X_eq T.ker.Pr T.ker.sel T.ker.S T.ker.tup T.ker.cst T.ker.idx hS.Pr hS.sel hS.S hS.tup
      hS.cst hS.idx
    rw [← htup] at h1 h2 h3
    exact ⟨hS.X_eq, rfl, hS.Pr.symm, hS.Ch.symm, hS.sel.symm, heq_of_eq hS.S.symm, h1, h2, h3, hS.m2.symm, hS.glob.symm, hS.amb.symm, rfl,
      hS.word.symm⟩
  wTie := fun u => heq_of_eq (hw u)
  lvTie := rfl
  sgTie := rfl
  v0 := InfinitePlace.mk B.embLL
  TU := tuOf I U
  xiVal := xiValOf I
  trIv := tr
  famEq := HEq.rfl
  gEq := rfl
  plEq := rfl
  i0Eq := rfl
  tEq := rfl
  muTie := fun _ => rfl
  ok1 := hOk
section Pins
variable {h hp l Z ht hJ hX U Xg tr} {hOk : (famC I hX U Xg tr).fam3.Ok3 1} {T : _root_.Formalism.L2.TiedDataSKAlt ex} {hS : I.StdKer l Z T.ker}
  {Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)}
  {R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp}
  {htup : R.I.tup = ixOf I U} {hw : ∀ u, R.I.wU u = u}
theorem lamOfCol_colK_eq_lamTrue : _root_.Formalism.L2.DIV.lamOfCol_alt (_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) = fun u i τ => B.wts.lamTrue u i τ := by
  funext u i τ
  exact congrArg (B.wts.lamTrue u i) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ)))
theorem colPins_colK' : _root_.Formalism.L2.DIV.ColumnCharactersCompatible (_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp R htup hw) where
  grpTie := HEq.rfl
  psTie := ⟨HEq.rfl, HEq.rfl⟩
  pointCharacterEq := ⟨HEq.rfl, HEq.rfl⟩
  wOk := (base_fields_primes_ok B X).2.2.1
  chOk := h.ch_ok
  hcTie := fun u τ => heq_of_eq (congrArg (B.hcW u) (eq_of_heq ((cast_heq _ _).trans (iT_heq l Z hS τ))))
  wtTie := by
    rw [_root_.GlobalTheory.Mem.R3.SelC.lamOfCol_colK_eq_lamTrue]
    exact ⟨_, _, wtTie_base I l Z T.ker⟩
  xgTie := fun χ => @mem_iff_XgE _ _ _ _ _ _ _ _ (_) B.embLL R.I.eG _ Xg hOk.ok2.irr R.tied.div.grp.e0 χ
  qNF := fun t => of_forall_ix ht (fun _ _ L => GlobalTheory.QNF.IdxMatNF L) (RcHyp.idxMatNF_of_isTw I h ht) t
  columnEvaluationOk := ⟨rowG_ok (Pr := B.primes X) B.wts I.Ch I.sel _ hX I.Ps (Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := B.fields) (S := I.S) I.sel), fun u => by
    have H := exists_read_fam (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
      I.Ps hOk.ok2 B.embLL (rowG_ok (Pr := B.primes X) B.wts I.Ch I.sel _ hX I.Ps (Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := B.fields) (S := I.S) I.sel))
      (A := (I.rec7 l Z).what₂.Amb) ((I.rec7 l Z).eMt u) R.I.tup R.tied.div.tup.mu0 R.tied.div.tup.inj R.I.jA
      (fun t => (R.tied.div.sharp.forms t).li) (fun t => (R.tied.div.sharp.forms t).span) R.Zs
    exact H⟩
end Pins
end Main
set_option maxHeartbeats 1000000 in
theorem exists_rowsKC_colPins_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL))
    (tr : TrI B X) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z))
    (Kc : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX),
    (famC I hX U Xg tr).fam3.Ok3 1 → ∀ (T : _root_.Formalism.L2.TiedDataSKAlt ex), I.StdKer l Z T.ker →
    ∀ (Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)) (P : Formalism.L2.Rows.RowSideFamily ex),
    P.Gp = Gc B X → HEq P.grp (inferInstance : Group (Gc B X)) → P.Pl0 = PlS B X → P.I0 = PlI B X → P.T = TupU I U →
    HEq P.A3 (famC I hX U Xg tr) → HEq P.P0 (lev0 I) → HEq P.ψ0 (chr0 I) → HEq P.Ps (lev1 I) → HEq P.ψs (chr1 I) →
    HEq P.I.tup (ixOf I U) → (∀ u, HEq (P.I.wU u) u) →
    ∀ Zs : DefSub (famC I hX U Xg tr).fam3.amb3, HEq P.Zs Zs → HEq P.Dc ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs) →
    HEq P.Sp (Sp Zs) →
    ∃ K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P, _root_.Formalism.L2.DIV.ColumnCharactersCompatible K ∧ HEq K.c (colRecK h hp l Z ht hJ hX U Xg tr T.ker) ∧ HEq K.Sp Sp ∧ HEq K.c.W B.wts ∧
      HEq (fun Zs => K.c.face Zs) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face ∧ HEq K.c.Xg Xg := by
  intro B X I h hp l Z ht hJ hX U Xg tr L hT Gi Gl Kc Y cX ex hOk T hS Sp P
  obtain @⟨Gp, grp, fin, Pl0, I0, Tt, A3, P0, ψ0, Ps, ψs, Zs', S0, S1, Dc, Sp', C, NuC, J, JA, JM, tied⟩ := P
  intro e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 Zs e13 e14 e15
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  subst e1 e3 e4 e5
  obtain rfl := eq_of_heq e2
  obtain rfl : fin = fintype_GLs B.fields.E (B.primes X).vGs B.R.r := Subsingleton.elim _ _
  cases e6
  cases e7
  cases e8
  cases e9
  cases e10
  cases e13
  cases e14
  cases e15
  exact ⟨_root_.GlobalTheory.Mem.R3.SelC.squareIntegrableColumnsOfKernel h hp l Z ht hJ hX U Xg tr hOk T hS Sp ⟨Zs, S0, S1, C, NuC, J, JA, JM, tied⟩ (eq_of_heq e11) fun u => eq_of_heq (e12 u),
    _root_.GlobalTheory.Mem.R3.SelC.colPins_colK', HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
end GlobalTheory.Mem.R3.SelC
end
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.Mem.R3.SelC
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
set_option maxHeartbeats 1000000 in
theorem jA_row_alt {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) (r : RXs t) (pin : ColPin w)
    (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (w.D Z) 𝔞 → χ 𝔞 = w.I.chi 𝔞) (a : w.I.ι) (ha)
    (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩) → B.LL) → Z.W.Amb a)
    (hj : SameOn (r.all.jA a) j) (Zs : DefSub (famT t).fam3.amb3)
    (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV ⟨w.I.tup a, ha⟩) → B.LL) :
    ∃ z : GlobalTheory.Core.Ht2.RowsK w.I a,
      z.1 = ((colRecC w.ok w.pins w.l Z pin.isTw pin.jets χ hχ t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).ev Zs ⟨w.I.tup a, ha⟩ F).1.1 ∧
      j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F) = r.e a (Df.toCx w.I t.hX a z) := by
  obtain ⟨z, ⟨F', hF', e1, e2⟩, e3⟩ := r.crd a ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) ⟨w.I.tup a, ha⟩).mulVec F)
  have e4 := evC_res_lvl (X := B.fields) (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel t.hX (InfinitePlace.mk B.embLL)
    (tuOf w.I (usedOf w.I T Wt)) t.r.z.Xg ∅ (xiValOf w.I) t.r.z.tr (TC.Ps w.I) t.r.intersectionNumber_baseChange.ok.ok2 Zs ⟨w.I.tup a, ha⟩ F
  have e5 := LinearEquiv.injective _ (eq_of_heq (e1.trans (heq_of_eq e4.symm)))
  refine ⟨z, ?_, (hj.2 _ _ fun i i' e => congrArg _ (Fin.ext e)).symm.trans e3⟩
  rw [e2]
  exact congrArg Subtype.val e5
variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem exists_readC_wU_eq_id (t : RowsT K w Z Wt ex.p0) (r : RXs t) (pin : ColPin w) (k : Formalism.L2.Ker.KerEntTied ex) (Sp Zsc) :
    ∃ C : ReadC t.r.z.R (reFace t.r.z.F
      (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Sp Zsc) ex.p0 t.r.Y,
      C.wU = fun u => u := by
  choose e he hn using exists_eNu w.ok w.l Z t.hX w.l0
  refine ⟨{ wU := fun u => u
            bij := Function.bijective_id
            eNu := e
            NuC := fun u => (Z.V.div.Nu u).L.comap ((e u).toLinearMap.restrictScalars (𝓞 B.LL))
            nu := fun u => ⟨(Submodule.map_comap_eq_of_surjective (f := (e u).toLinearMap.restrictScalars (𝓞 B.LL)) (e u).surjective _).symm, he u⟩
            pt := fun u s x F => ?_ }, rfl⟩
  have key : ∀ (a : w.I.ι) (s : TupU w.I (usedOf w.I T Wt)) (_ : w.I.tup a = s.1)
      (j : (Fin (rDim (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s) → B.LL) → Z.W.Amb a) (_ : SameOn (r.all.jA a) j)
      (Zs : DefSub (famT t).fam3.amb3) (F : Fin (((famT t).side3 (lev1 w.I) (chr1 w.I) Zs).nV s) → B.LL),
      B.embLL (((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr k).face Zs).Pt u s x F) =
        Z.W.perCol u a (Z.V.jN u (e u x)) (j ((rV0 (w.st Z).toD7 (famT t).A (lev1 w.I) (chr1 w.I) s).mulVec F)) := by
    rintro a ⟨τ, ha⟩ (rfl : w.I.tup a = τ) j hj Zs F
    obtain ⟨z, hz, e1⟩ := _root_.GlobalTheory.Mem.R3.SelC.jA_row_alt t r pin k.χ (ker_chi_eq w.I w.l Z k) a ha j hj Zs F
    rw [e1]
    exact face_pt w.ok w.pins w.l Z pin.isTw pin.jets k.χ (ker_chi_eq w.I w.l Z k) t.hX w.l0 r.e r.eMt0 r.eMtTw _ _ _ Zs u a ha x _
      (hn u x) F z hz
  exact key (t.r.Y.tup s) s ((congrArg w.I.tup (t.r.tup_ix s)).trans (tup_ixOf w.I s)) (t.r.Y.jA s) (r.jA_use s) _ F
set_option maxHeartbeats 400000 in
theorem args_pinned_heq_zsOf_mem_eq (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) :
    (a.x.G = Gc B w.px ∧ HEq a.x.grp (inferInstance : Group (Gc B w.px)) ∧ a.x.Pl0 = PlS B w.px ∧ a.x.I0 = PlI B w.px ∧
      a.x.T = TupU w.I (usedOf w.I T Wt) ∧ HEq a.x.A3 (famC w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr)) ∧
    (HEq a.x.F.P0 (lev0 w.I) ∧ HEq a.x.F.ψ0 (chr0 w.I) ∧ HEq a.x.F.P1 (lev1 w.I) ∧ HEq a.x.F.ψ1 (chr1 w.I) ∧ HEq a.x.F.Dc a.Dc ∧
      HEq a.x.F.Sp a.Sp) ∧
    ∃ Zs : DefSub (famT t).fam3.amb3, HEq (zsOf a.x.R a.x.F) Zs ∧ HEq (a.x.F.Dc (zsOf a.x.R a.x.F)) (a.Dc Zs) ∧
      HEq (a.x.F.Sp (zsOf a.x.R a.x.F)) (a.Sp Zs) ∧ (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = (a.Dc Zs).Mem :=
  ⟨by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).1, by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).2.1,
    zsOf ((t.r.z.R.updS t.r.z.R.kap a.lam).withErr a.err) (reFace t.r.z.F a.Dc a.Sp a.Zsc),
    by kexactB (@pack_heq (w.st Z).toD7 _ _ a.pack).2.2⟩
set_option maxHeartbeats 400000 in
theorem exists_square_integrable_columns_of_data (t : RowsT K w Z Wt ex.p0) (pin : ColPin w) (S : _root_.Formalism.L2.TiedDataSKAlt ex) (hS : TC.StdKer w.I w.l Z S.ker)
    (a : TwArgs ex t) (hD : a.Dc = (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    (hw : HEq a.x.C.wU fun u : B.Word => u) :
    ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns S (divisionPairOfAdelicFormsFaceColumnsData a.x), HEq (fun Zs => C.c.face Zs) a.x.F.Dc ∧ HEq C.Sp a.x.F.Sp ∧ HEq C.c.W B.wts ∧
      HEq C.c.Xg t.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, g11, g12⟩, Zs, g13, g14, g15, g16⟩ := _root_.GlobalTheory.Mem.R3.SelC.args_pinned_heq_zsOf_mem_eq t a
  obtain ⟨Sp, hSp⟩ : ∃ Sp : ∀ Zs, SPer ((colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face Zs),
      HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
    have key : ∀ Dc : type_of% a.Dc, a.Dc = Dc → ∃ Sp : ∀ Zs, SPer (Dc Zs), HEq a.Sp Sp ∧ ∀ Zs, HEq (a.Sp Zs) (Sp Zs) := by
      rintro _ rfl
      exact ⟨a.Sp, HEq.rfl, fun _ => HEq.rfl⟩
    exact (key (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face hD)
  have e1 := congrFun hD Zs
  have e2 : (a.x.F.Dc (zsOf a.x.R a.x.F)).Mem = B.Word := by kexactB g16.trans (congrArg DefCols.Mem e1)
  have e3 : HEq a.x.Y.tup (ixOf w.I (usedOf w.I T Wt)) := by kexactB a.tup.trans (heq_of_eq (funext t.r.tup_ix))
  have e4 : ∀ u, HEq (a.x.C.wU u) u := fun u => heq_app e2 hw u
  have e5 := g14.trans (heq_of_eq e1)
  have e6 := g15.trans (hSp.2 Zs)
  obtain ⟨C, c1, -, c3, c4, c5, c6⟩ := _root_.GlobalTheory.Mem.R3.SelC.exists_rowsKC_colPins_alt w.I w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr
    L hT Gi Gl Kc Yd cX ex t.r.intersectionNumber_baseChange.ok S hS Sp (divisionPairOfAdelicFormsFaceColumnsData a.x) ((h1)) ((h2)) ((h3)) ((h4)) ((h5))
    ((h6)) ((h7)) ((h8)) ((h9)) ((h10)) ((e3)) ((e4)) Zs ((g13))
    ((e5)) ((e6))
  have d1 := (heq_of_eq hD.symm).trans g11.symm
  refine ⟨_root_.GlobalTheory.Cp.SquareIntegrableColumns.ofS C, HEq.trans (b := (colRecK w.ok w.pins w.l Z pin.isTw pin.jets t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr S.ker).face)
    ?_ ?_, ?_, ?_, ?_, ?_⟩
  · exact (c5)
  · exact (d1)
  · kexactB c3.trans (hSp.1.symm.trans g12.symm)
  · exact (c4)
  · exact (c6)
  · exact (c1)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem square_integrable_columns_of_witnesses : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex), KPin q t → Nonempty (RXs q.x.what₂) → ∃ Dc Sp₀ Zsc₀, ∃ C₀ : ReadC q.x.what₂.r.z.R (reFace q.x.what₂.r.z.F Dc Sp₀ Zsc₀) q.O.ex.p0 ((q.x.what₂.r.Y)), ∀ (T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex), T.ker = t → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → a.Dc = Dc → HEq x.C.wU C₀.wU → HEq x.C.eNu C₀.eNu → ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  intro 𝒮 K q t hk ⟨r⟩
  obtain ⟨C₀, hC⟩ := _root_.GlobalTheory.Mem.R3.SelC.exists_readC_wU_eq_id (ex := q.O.ex) q.x.what₂ r q.x.pin t (fun _ => ⟨ℂ, inferInstance, inferInstance, fun _ => 0, ⊥⟩)
    q.x.what₂.r.z.F.Zsc
  refine ⟨_, _, _, C₀, fun S hS a x hx hD hw _ => ?_⟩
  subst hS
  cases hx
  exact _root_.GlobalTheory.Mem.R3.SelC.exists_square_integrable_columns_of_data (ex := q.O.ex) q.x.what₂ q.x.pin S hk.std a hD (hw.trans (heq_of_eq hC))
end GlobalTheory.Mem.R3.SelC
end
end
