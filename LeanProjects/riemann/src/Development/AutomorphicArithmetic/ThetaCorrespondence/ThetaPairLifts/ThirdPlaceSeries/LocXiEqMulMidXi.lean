import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
noncomputable section
namespace GlobalTheory.Fam.MidLoc
open Formalism.L2.Col (IntAt redP qOf)
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
end Loc
section Comparison₂
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Comparison₂
section Mat
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
end Mat
section Tuple
open Formalism.L2.Col
end Tuple
section World
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
set_option maxHeartbeats 1000000 in
theorem exists_sameData_atType (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (hϖ : valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((qOf (a.pl n).1 : ℕ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) :
    ∃ S' : SymData (a.G n).k (a.G n).s B.R.k, SameData S' (a.G n).S B.R.t (a.G n).ν ∧
      ∀ (b : I.ι) (P : BadPr I b), P.1 = (a.pl n).1 →
        AtType I.Ch I.sel (I.tup b) (I.cst b) B.embLL P ((a.G n).q.pr.comp (incA (I.rec7 l Z))) S' := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain ⟨hid, hv⟩ := hR.idem n
  obtain ⟨hi, hd⟩ := SymChainAt.place_facts (a.G n).q hid
  have hPm : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
  obtain ⟨i, g1, g2, -, g4, -⟩ := LevelData.type_prime hPm
  obtain ⟨ϖ, hϖq, -⟩ := LevelData.exists_unif (ι := (a.G n).q.pr.comp (incA (I.rec7 l Z))) hi hd (g1 ▸ g4)
  obtain ⟨S', e1, e2, e3, e4, e5⟩ := exists_normal (a.G n).S ϖ
    (by rw [hϖq, map_natCast, Valuation.map_sub_swap]; exact hϖ) B.R.t (a.G n).ν
  refine ⟨S', e5, fun b P hP => ?_⟩
  obtain ⟨PP, hPP⟩ := P
  obtain rfl : PP = (a.pl n).1 := hP
  have ok := hW.tr.ok
  have hok := ok.idx_ok b
  have f1 : Formalism.L2.Col.psi0P I.Ch (a.pl n).1 = I.Ch.psi0 ⟨_, hPm⟩ := dif_pos hPm
  have f2 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 = Formalism.L2.Col.chiAt I.Ch ⟨_, hPm⟩ := dif_pos hPm
  refine ⟨hPm, hs.symm, hok.cst_ok, ok.sharp _, by rw [hW.tr.tw.cst_eq]; exact Nat.le_succ _,
    fun x hx => hok.psi0 ⟨_, hPP⟩ x hPm hx, ⟨hi, hd, rfl, e1 ▸ hϖq⟩, fun x hx => ?_, fun j x v h1 h2 h3 => ?_⟩
  · rw [e2]
    exact psi_tie (a.G n).q hv hi hd (g1 ▸ g2) (g1 ▸ g4) (hok.xiUnitAtPrime ⟨_, hPP⟩).1 (_root_.GlobalTheory.Fam.pk_z W).ψ W.Q.stdChar B.embLL _
      (fun z c h => f1 ▸ ok.weil ⟨_, hPm⟩ z c h) _ (a.G n).char x hx
  · rw [Formalism.L2.Col.LocE.unitV, dif_pos h2]
    by_cases hj : j < B.R.m
    · rw [e3 _ (by omega)]
      have key := chi_tie (a.G n).q hid hi hd (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta (j + 1)
        (c := (Units.map (B.embLL : B.fields.K →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch (a.pl n).1 j)) (hW.tr.chr ⟨j, hj⟩)
        (fun y x c hx hy => Units.ext (by
          have h := hok.mu0G ⟨j, hj⟩ ⟨_, hPm⟩ x y c hx hy
          have e3 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = I.Ch.chi ⟨j, hj⟩ ⟨_, hPm⟩ := (congrFun f2 j).trans (dif_pos hj)
          rw [e3]
          exact h.symm))
        W.Q.charW.base.lev.eta
        (fun y x c hx hy => ((_root_.GlobalTheory.Fam.pk_z W).C.isEta.unr (a.pl n).1 _ (by
          have hy' : y ∉ (a.pl n).1.asIdeal := fun h => by
            haveI := (a.pl n).1.isPrime
            exact c.ne_zero (hy.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
          change Valued.v (((x : (I.rec7 l Z).host.E)) : (a.pl n).1.adicCompletion (I.rec7 l Z).host.E) = 1
          rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hx]
          exact ((a.pl n).1.valuation_eq_one_iff_notMem (K := (I.rec7 l Z).host.E)).2 hy')).symm)
        _ (hR.mu n (j + 1) (by omega) hj) x v h2.unit h1 rfl h3
      rw [key]
      rfl
    · rw [e4 _ (by omega), ((congrFun f2 j).trans (dif_neg hj) : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = 1)]
      simp
end World
section Main
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def intermediateXiValue (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (n : Fin a.n) (j c : ℕ) (H : j + 1 + c = (a.G n).s)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E) : ℂ :=
  ((a.G n).S.T (Fin B.R.t)).entry (a.G n).S.ψ (a.G n).ν j c H 1 1
    (((a.G n).FX (j + 1) (by omega)).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX j (by omega)).β)
theorem midXi_isLocFac' {a : _root_.GlobalTheory.Fam.GeometricFamily W u} (ha : a.Is) (hat : a.True) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (j c : ℕ) (H : j + 1 + c = (a.G n).s) :
    IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) (_root_.GlobalTheory.Fam.MidLoc.intermediateXiValue a n j c H) := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hid := (hR.idem n).1
  have hpf := SymChainAt.place_facts (a.G n).q hid
  have hL : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L ∧
      ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun j hj => ⟨(ha.x j hj).sd, Set.ext (hat.pinX.xs j hj).2.2⟩
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, _, _, _, hpf.2, hid,
    StdMatch.int_iff_up_mem (a.G n).q (a.G n).unit _ _ (hL _ (by omega)).1 (hL _ (by omega)).1 (hL _ (by omega)).2
      (hL _ (by omega)).2 ((a.G n).latX _ _) ((a.G n).latX _ _),
    (SB _).smul_mem _ (opE_mem_SB 1 _ _ (om_mem_SB _ _ _ ((Chain.ofType_regular _ _ _ _ _).1 _ _ _))), (a.G n).cg_mid j c H,
    fun _ => rfl⟩
set_option maxHeartbeats 1000000 in
theorem locXi_eq_mul_midXi_alt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {a : _root_.GlobalTheory.Fam.GeometricFamily W u} (ha : a.Is) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (hϖ : valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((qOf (a.pl n).1 : ℕ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k))
    (j c : ℕ) (H : j + 1 + c = (a.G n).s) (hj : j + 1 ≤ B.R.m) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)) (P : BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ z, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (homOf I l Z j hj z)) = C * _root_.GlobalTheory.Fam.MidLoc.intermediateXiValue a n j c H z := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  by_cases h0 : ∃ (b : I.ι) (P : BadPr I b), P.1 = (a.pl n).1
  swap
  · exact ⟨1, one_ne_zero, fun t _ _ _ _ P hP => absurd ⟨_, P, hP⟩ h0⟩
  obtain ⟨b₀, P₀, hP₀⟩ := h0
  obtain ⟨S', hS, hA⟩ := _root_.GlobalTheory.Fam.MidLoc.exists_sameData_atType hW a hR n hϖ
  obtain ⟨e', he', hF'⟩ := (ha.stdG n).1 j (by omega)
  obtain ⟨e, he, hF⟩ := (ha.stdG n).1 (j + 1) (by omega)
  have hr' := rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)
  have hr := rankN (I.rec7 l Z) (j + 1) hj
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.EntryBridge.entry_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol (hA b₀ P₀ hP₀) j c H
    (e'.trans (finCongr hr')) (e.trans (finCongr hr)) he' he
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ P hP z => ?_⟩
  have hPv : P.1 ∈ (B.primes X).vGs := (hA _ P hP).mem
  have hh : ∀ i b, (I.idx (W.P.I.tup t)).h i b P = 1 := by
    rw [(hW.tr.tw (W.P.I.tup t)).2]
    exact fun i b => StdMatch.twSt_h _ _ _ _ _ _ b P hPv
  have hlt := LevelData.val_lt_one_iff (hA _ P hP).tie.compl.int
  have hfr : ∀ i, i + 1 < B.R.m → ∀ β r s, _ := fun i hi β r s => (hlt _).2 (frame_cong hW.tr.ok (J.A.p0 i β).1.1
    (hJ.std i hi β ▸ (hJ.is.base i (by omega) β).1) P hPv r s)
  obtain ⟨g, hg, g', hg', hz⟩ := toLoc_inFr ((a.G n).q.pr.comp (incA (I.rec7 l Z))) hr' hr _ _ e' e hF' hF _ _
    (hfr j (by omega) (J.ι j α)) (hfr (j + 1) (by omega) (J.ι (j + 1) γ))
  have key := (congrArg _ (hz z)).symm.trans (hC _)
  rw [hS.1, hW.tr.tw.cst_eq, xiAt_tw_eq _ _ _ _ _ P₀ P (hP₀.trans hP.symm) (hA _ P₀ hP₀).mem] at key
  replace key := (entry_mul_KOne (a.G n).S (Fin B.R.t) (a.G n).ν j c H hg hg' _).symm.trans key
  unfold locXi
  rw [dif_pos (by omega), hh, hh, eq_inv_mul_iff_mul_eq₀ hC0]
  exact (congrArg (fun y => C * B.embLL (Formalism.L2.Col.XiAt I.Ch I.sel (I.tup (W.P.I.tup t)) y j P 1 1 _))
    (hW.tr.tw.cst_eq (W.P.I.tup t))).trans key.symm
end Main
end GlobalTheory.Fam.MidLoc
end
end
