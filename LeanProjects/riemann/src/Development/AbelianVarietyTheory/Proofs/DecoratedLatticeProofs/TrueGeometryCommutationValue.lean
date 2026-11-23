import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsLow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousOfCond
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentatives
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleAdelicDataStandardBasePointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceGeometryExtensionCosetOrbitRepsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsExtGeometryTupleOfRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExpStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepInverseCharacterLocalComponentChainTameStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowJoin

open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

theorem idxProd (hI : I.Ok) (hT : I.IsTw) (a : I.ι) : IdxProd I.sel (I.tup a) (I.cst a) (I.idx a) := by
  have h := hI.idx_ok a
  rw [(hT a).2] at h ⊢
  exact GlobalTheory.T.twistIndexData_representative_dependsOnDoubleCoset _ _ _ _ _ _ _ _ _ _ h

theorem h_one (hT : I.IsTw) (a : I.ι) : ∀ j b (P : BadPr I a), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1 := by
  rw [(hT a).2]
  exact Formalism.L2.Col.twSt_h_g I.Ch I.sel (I.tup a) (I.cst a) _

theorem get_bij {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} (hA : A.Is) (j : ℕ) (hj : j + 1 < B.R.m) :
    Function.Bijective fun β : Ch₀ j => (A.b0 j β).get (by omega) := by
  have h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, cosetIn p = fun _ => ∅ := fun p => by
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj.ne] at h
    funext P
    rw [cosetIn, show p.1.2 = ∅ from h]
    simp
  refine ⟨fun β β' e => hA.chart_ext j (by omega) β β' ?_ ((h0 _).trans (h0 _).symm), fun b => ?_⟩
  · rw [← (A.b0 j β).of_get (by omega) (by omega), ← (A.b0 j β').of_get (by omega) (by omega)]
    exact congrArg (Idx.of · _) e
  · haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
    letI := B.fields.starE
    obtain ⟨p, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := j) (Formalism.L2.Col.DecoF.base _ _ _ _ _)
    refine ⟨A.chOf j ((I.stp u a j).cl (Idx.of b (by omega)) p), ?_⟩
    exact Idx.get_eq (congrArg Subtype.val (hA.rep j (by omega) _).1.symm) _

section Place

variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}

structure Good (P : BadPr I a) (G : QGeo v Bs PP) {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ) (hψ : Continuous G.ψk)
    (sg : ℂ) : Prop where
  sign : sg = 1 ∨ sg = -1
  tw : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg)
  M : E.M = (I.cst a).M
  up : ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j))
  rat : ∀ j d h, Nonempty ((I.idx a).β j) → E.A j d h =
    {g | ∃ b, IsGL (X := B.fields) (R := B.R) (k := G.k) (G.q.pr.comp (incA (I.rec7 l Z))) ((I.idx a).h j b P) g}
  next : ∀ j d (h : j + 1 + d = G.s), Nonempty ((I.idx a).β j) → (E.A (j + 1) d h).Nonempty →
    ∃ γ : Formalism.L2.Col.AutY B.fields B.R (j + 1), Bdd (B.primes X) (j + 1) P.1 γ ∧
      ∃ al, Formalism.L2.Col.FiniteSumNonzeroLargeDepth I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j al P) γ

set_option maxHeartbeats 1000000 in

theorem exists_good (hI : I.Ok) (hT : I.IsTw) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs) (G : QGeo v Bs PP) (heq : PP = P.1) (hc : c.Is)
    (hstd : IsStdChar (I.rec7 l Z) c.ψ (-1)) (χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle)
    (hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (χ j) (I.C.mu0 ⟨j, hj⟩ * I.xi a)) :
    ∃ (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ), Good P G E hψ sg := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have hcp : GlobalTheory.SymBridge.IsCompl (E := B.fields.E) P.1 (Formalism.L2.Col.qOf P.1) (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ := heq ▸ G.compl
  have hid : Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) G.q.e P.1 := heq ▸ G.idem
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = G.s by omega] at hL
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split (I.rec7 l Z) G.k (ofSplit G.q) c.ψ hstd
  choose μ hμ using fun j => hcomp (χ (j - 1))⁻¹
  have hψ := continuous_of_cond G.cond
  have hd := TC.degOne_of_ok hI a P
  obtain ⟨⟨ϖ, unif, ψ, cont, cond, δ, tame, η, unr, sg⟩, hA, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.exists_completionTwistData_chainColumns _ _ _ _ _ _ _ _ _ _ _ hL P hP G.k (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ hcp G.unif G.ψk hψ G.cond
      (GlobalTheory.T.weilCharacter_splitDegreeOne_place_eq_exp (I.rec7 l Z) G.k G.q P.1 hid hd.1 hd.2 hcp.int c.ψ hstd G.ψk G.char) μ
      fun i hi => GlobalTheory.T.step_inverse_character_local_component_chain_tame I hI l Z a P hP G.k G.q hid hcp.int hcp.dense i hi (χ i) (hχ i hi) _ (hμ (i + 1))
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  have hM : G.s + 1 ≤ (I.cst a).M := by
    rw [hT.cst_eq]
    show _ ≤ B.R.m
    omega
  obtain ⟨A, a1, a2, a3, a4⟩ := exists_system G.unitVol hA hL (idxProd hI hT a) hM
  have hmu : ∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ) := fun j hj => by
    rw [h3 j (by omega)]
    exact hμ (j + 1)
  obtain ⟨E₀, rfl, rfl, rfl, e4⟩ := GlobalTheory.T.exists_extGeometry_tuple_of_representatives _ c v Bs _ G χ hc δ tame η unr hmu A a1 _ a2
  obtain ⟨E, e1, e2, e3, e5, -, e6⟩ := GlobalTheory.T.exists_splitPlaceGeometryExtension_cosetOrbitReps _ c v Bs _ G χ hc _ tame _ unr hmu _ a1 _ a2 (E₀.Ch (G.s + 1))
    (fun y => (E₀.cos y).out ∘ id) (fun y y' h => E₀.cos_inj y y' (by
      rw [← e4] at h
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using h))
    (fun z hz => by
      rw [← e4] at hz ⊢
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using E₀.cos_all z hz)
  refine ⟨E, hψ, sg, h4, ?_, e5, e6, e3 ▸ a3, e3 ▸ a4⟩
  have e7 : E.tw hψ sg = ⟨G.ϖ, unif, G.ψk, cont, cond, E₀.δ, tame, E₀.η, unr, sg⟩ := by simp only [QExt.tw, e1, e2]
  rw [e7]
  exact hA

theorem res_of_tw (hI : I.Ok) {hP : PP ∈ Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)} {G : QGeo v Bs PP} {W : TwData G.k}
    (h : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL ⟨PP, hP⟩ (G.q.pr.comp (incA (I.rec7 l Z))) G.s W)
    {ξ : (kP PP)ˣ →* ℂˣ} (hξ : IsRes (I.xi a) PP ξ) : G.Res W.δ ξ := by
  intro z x r hx hr
  have h0 : (z : (I.rec7 l Z).host.E) ≠ 0 := fun e => x.ne_zero (by rw [hx, e]; exact (G.q.pr.comp (incA (I.rec7 l Z))).map_zero)
  have h1 : Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E) = (r : kP PP) := (Formalism.L2.Col.reduction_coe PP z).trans hr.symm
  have h2 : IsUnit (Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E)) := h1 ▸ r.isUnit
  have h3 : Formalism.L2.Col.IntAt PP (z : (I.rec7 l Z).host.E) :=
    ⟨z, 1, fun e => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 e), by simp⟩
  have h4 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads a)
    (GlobalTheory.Mem.ReadTwist.tameAt (hI.xi_reads a) fun v => Subgroup.mem_iInf.1 (I.tup a).2.1.2 v) PP h2.unit z (Units.mk0 _ h0) rfl
    (hr.symm.trans h1.symm)
  refine Units.ext ((h.del _ x h3 h2 hx).trans ?_)
  rw [hξ z (Units.mk0 _ h0) r rfl hr, Units.val_inv_eq_inv_val]
  exact congrArg _ ((congrArg _ (dif_pos h2)).trans h4)

end Place

set_option maxHeartbeats 2000000 in

theorem exists_readsLow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (commOf (pk W) u a.g).Is → ∀ t, ∃ J : QJ a t, J.ReadsLow := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ ha hc t
  have hI := hW.tr.ok
  have hm := B.R.two_le_m
  obtain ⟨Ch₀, -, A, hA, hlast, hne, -, hstd, -⟩ := GlobalTheory.T.exists_tupleAdelicData_standardBasePoints I hI hW.tr.pins.some l Z u (W.P.I.tup t)
  have hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (chrK W t j) (I.C.mu0 ⟨j, hj⟩ * I.xi (W.P.I.tup t)) := fun j hj =>
    GlobalTheory.Mem.TupChar.chrEq_mul (hW.tr.chr ⟨j, hj⟩) (hW.tq.xi t)
  let e := ((pk W).Q t).equivFin
  let pl : Fin ((pk W).Q t).card → Pl (I.rec7 l Z).host.E := fun i => (e.symm i).1
  have mem : ∀ i, pl i ∈ (pk W).Q t := fun i => (e.symm i).2
  have plinj : Function.Injective pl := Subtype.val_injective.comp e.symm.injective
  have plsurj : ∀ PP ∈ (pk W).Q t, ∃ i, pl i = PP := fun PP h => ⟨e ⟨PP, h⟩, by simp [pl]⟩
  let P : Fin ((pk W).Q t).card → BadPr I (W.P.I.tup t) := fun i => ⟨pl i, Finset.mem_union_right _ ((hW.tq.Q t _).1 (mem i))⟩
  have hoff : ∀ i, (P i).1 ∉ (B.primes X).vGs := fun i => TC.Q_notMem_of_ok hI _ _ ((hW.tq.Q t _).1 (mem i))
  let G := fun i => a.Q (pl i) ⟨t, mem i⟩
  have hs : ∀ i, (G i).s + 1 + 1 = B.R.m := fun i => (G i).hs
  choose E hψ sg hE using fun i => exists_good hI hW.tr.tw (P i) (hoff i) (G i) rfl hc ha.pinX.std (chrK W t) hχ
  let Rel : ∀ i j, Formalism.L2.Col.AutY B.fields B.R j → (E i).Ch j → Prop := fun i j γ y => ∀ d (h : j + d = (G i).s),
    IsGL (X := B.fields) (R := B.R) (k := (G i).k) ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y)
  have hrel : ∀ i j d (h : j + d = (G i).s) γ y, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
      ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y) → Rel i j γ y := fun i j d h γ y h1 d' h' => by
    obtain rfl : d' = d := by omega
    exact h1
  have hd : ∀ i j, j ≤ B.R.m - 2 → ∃ d, j + d = (G i).s := fun i j hj => ⟨(G i).s - j, by have := hs i; omega⟩
  have hbij := exists_bij (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hI.ch_ok hI.sel_ok (hI.sharp _) (hI.idx_ok (W.P.I.tup t))
    (GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives _ _ _ _ _ _ _ _ _ _ _ (hI.idx_ok _) (idxProd hI hW.tr.tw _)) (h_one hW.tr.tw _) P
    (fun i i' h => plinj (congrArg (fun Q : BadPr I (W.P.I.tup t) => Q.1) h)) hoff
    (fun Q hQ => (plsurj Q.1 ((hW.tq.Q t _).2 ((Finset.mem_union.1 Q.2).resolve_left hQ))).imp fun i h => Subtype.ext h)
    (fun i => (E i).Ch) Rel
    (fun i j hj b => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_completionMatrix_of_rationalTwistAut B.fields B.R (G i).k ((G i).q.pr.comp (incA (I.rec7 l Z))) j (d + 1)
        (by have := hs i; simp only [Formalism.L2.Col.cOf]; omega) ((I.idx _).h j b (P i))
      obtain ⟨y, -, rfl⟩ := ((E i).rep_bij j d h).surjOn (((hE i).rat j d h ⟨b⟩).ge ⟨b, hg⟩)
      exact ⟨y, hrel i j d h _ _ hg⟩)
    (fun i j hj h0 y => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨b, hb⟩ := ((hE i).rat j d h h0).le (((E i).rep_bij j d h).mapsTo (Set.mem_univ y))
      exact ⟨b, hrel i j d h _ _ hb⟩)
    (fun i j hj γ γ' y y' h1 h2 => by
      obtain ⟨d, h⟩ := hd i j hj
      exact (isGL_unique (h1 d h) (h2 d h)).trans
        ⟨fun e => ((E i).rep_bij j d h).injOn (Set.mem_univ _) (Set.mem_univ _) e, fun e => e ▸ rfl⟩)
    (fun i j hj h0 ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      exact (hE i).next j d h h0 ⟨_, ((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)⟩)
    (fun i j hj ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      obtain ⟨g, hg, -⟩ := Set.mem_iUnion₂.1
        (((E i).reps.bij j d h).mapsTo (((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)))
      obtain ⟨y', -, -⟩ := ((E i).rep_bij j _ _).surjOn hg
      exact ⟨y'⟩)
  have hup : ∀ j, B.R.m ≤ j → ∀ i, Nonempty (Unique ((E i).Ch j)) := fun j hj i => by
    rcases hj.eq_or_lt with h | h
    · rw [← h, ← hs i]
      exact Fintype.card_eq_one_iff_nonempty_unique.1 (E i).one
    · exact (hE i).up j (by rw [hs i]; exact h)
  have key : ∀ j, ∃ (π : ∀ i, Ch₀ j → (E i).Ch j) (ι : (∀ i, (E i).Ch j) → Ch₀ j),
      (∀ i d (h : j + d = (G i).s) (hj : j < B.R.m) β, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
        ((G i).q.pr.comp (incA (I.rec7 l Z))) ((I.idx (W.P.I.tup t)).h j ((A.b0 j β).get hj) (P i)) ((E i).rep j d h (π i β))) ∧
      (j + 1 ≠ B.R.m → (∀ y i, π i (ι y) = y i) ∧ (j ≤ B.R.m → Function.Surjective ι)) := by
    intro j
    rcases lt_trichotomy (j + 1) B.R.m with hj | hj | hj
    · obtain ⟨φ, h1, h2⟩ := hbij j (by omega)
      let f := Equiv.ofBijective _ (h1.comp (get_bij hA j hj))
      exact ⟨fun i β => f β i, f.symm, fun i d h _ β => h2 _ i d h, fun _ =>
        ⟨fun y i => congrFun (f.apply_symm_apply y) i, fun _ => f.symm.surjective⟩⟩
    · have h1 : ∀ i, Nonempty ((E i).Ch j) := fun i => by
        rw [show j = (G i).s + 1 by have := hs i; omega]
        exact ⟨((E i).cos_all 0 (zero_mem _)).choose⟩
      have h2 : Nonempty ((I.idx (W.P.I.tup t)).β j) := by
        rw [show j = B.R.m - 2 + 1 by omega]
        exact ⟨(hI.idx_ok _).last_uniq.choose⟩
      exact ⟨fun i _ => (h1 i).some, fun _ => (hne j ⟨Idx.of h2.some (by omega)⟩).some,
        fun i d h => by have := hs i; omega, fun h => absurd hj h⟩
    · have h1 := fun i => (hup j (by omega) i).some
      refine ⟨fun i _ => default, fun _ => (hne j ⟨Idx.top _ _ _ (by omega)⟩).some, fun i d h hj' => by omega,
        fun _ => ⟨fun y i => Subsingleton.elim _ _, fun hj' β => ⟨default, ?_⟩⟩⟩
      obtain rfl : j = B.R.m := by omega
      exact hlast.some.instSubsingleton.elim _ _
  choose π ι k1 k2 using key
  refine ⟨⟨Ch₀, A, _, pl, mem, E, P, hψ, sg, fun i j => π j i, ι⟩, hA, plinj, plsurj,
    fun j hj => (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (hA.chr ⟨j, hj⟩) (hχ j hj), fun i => ?_, fun _ => rfl,
    fun i => (hE i).sign, fun i => (hE i).tw, fun i => (hE i).M, fun i j => k1 j i, hstd, hlast, fun j _ hj => (k2 j hj).1,
    fun j hj y y' h => funext fun i => ?_, (k2 0 (by omega)).2 (by omega), (k2 _ (by omega)).2 le_rfl,
    fun j hj hj' γ hγ => absurd ((k2 _ hj').2 hj γ) hγ⟩
  · exact res_of_tw hI (hE i).tw (hW.lev.2.2 t ▸ hW.pk.bot.hyp.2.2.2.1.lev.xiR t _ (mem i))
  · exact ((k2 j hj).1 y i).symm.trans ((congrArg (π j i) h).trans ((k2 j hj).1 y' i))

end GlobalTheory.LowJoin

end
