import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsLow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LowJoin
open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
section Place
variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}
end Place
set_option maxHeartbeats 2000000 in
theorem exists_quadratic_extension_readsLow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ ha hc t
  have hI := hW.tr.ok
  have hm := B.R.two_le_m
  obtain ⟨Ch₀, -, A, hA, hlast, hne, -, hstd, -⟩ := GlobalTheory.T.exists_tupleAdelicData_standardBasePoints I hI hW.tr.pins.some l Z u (W.P.I.tup t)
  have hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (_root_.GlobalTheory.Fam.chrK_alt W t j) (I.C.mu0 ⟨j, hj⟩ * I.xi (W.P.I.tup t)) := fun j hj =>
    GlobalTheory.Mem.TupChar.chrEq_mul (hW.tr.chr ⟨j, hj⟩) (hW.tq.xi t)
  let e := ((_root_.GlobalTheory.Fam.pk_z W).Q t).equivFin
  let pl : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → Pl (I.rec7 l Z).host.E := fun i => (e.symm i).1
  have mem : ∀ i, pl i ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t := fun i => (e.symm i).2
  have plinj : Function.Injective pl := Subtype.val_injective.comp e.symm.injective
  have plsurj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, pl i = PP := fun PP h => ⟨e ⟨PP, h⟩, by simp [pl]⟩
  let P : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → BadPr I (W.P.I.tup t) := fun i => ⟨pl i, Finset.mem_union_right _ ((hW.tq.Q t _).1 (mem i))⟩
  have hoff : ∀ i, (P i).1 ∉ (B.primes X).vGs := fun i => TC.Q_notMem_of_ok hI _ _ ((hW.tq.Q t _).1 (mem i))
  let G := fun i => a.Q (pl i) ⟨t, mem i⟩
  have hs : ∀ i, (G i).s + 1 + 1 = B.R.m := fun i => (G i).hs
  choose E hψ sg hE using fun i => exists_good hI hW.tr.tw (P i) (hoff i) (G i) rfl hc ha.pinX.std (_root_.GlobalTheory.Fam.chrK_alt W t) hχ
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
end
