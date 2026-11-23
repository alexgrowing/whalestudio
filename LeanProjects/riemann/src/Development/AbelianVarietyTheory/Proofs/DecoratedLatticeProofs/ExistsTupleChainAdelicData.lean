import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryLiftOfChartBasePointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepChartBasePointCarriesStdPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStepPointOfChartBasePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.TupEx

section RK
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.Col2.MemChart
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem kStd_at_SQ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (n : ℕ) (P : HeightOneSpectrum (𝓞 B.host.E))
    (hP : P ∈ I.SQ) : (kStd X u n).1.map (adAt B.host.F P) = 1 := by
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨b, hb⟩ := (ColIn.mem_SQ (I := I)).1 hP
  have hT := GlobalTheory.Mem.Col2.ChEx.T_notMem_qv I hI hPr u b ⟨P, hb⟩
  exact GlobalTheory.Mem.Col2.TopPtModel.adAt_of_prV P ((kStd_spec hPr u n).2.1 _ hT)

end RK

section RK2
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.Col2.MemChart
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem kStd_pt {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) :
    ∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, TC.PtOf (kStd X u (B.R.N i)) q := by
  have hPr := (base_fields_primes_ok B X).2.1
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  obtain ⟨⟨p, hp, -⟩, -, -⟩ := kStd_spec hPr u (B.R.N i)
  refine GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat B.sp.cm _ _ _ _ hp.uni fun P hP => ⟨1, fun r s => ?_⟩
  have h := congrFun (congrFun (kStd_at_SQ I hI u (B.R.N i) P (ColIn.Q_subset_SQ (I := I) a hP)) r) s
  rw [Matrix.map_apply] at h
  rw [h, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end RK2

section BO
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE

def BaseOk {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (k : TC.GA B (B.R.N i)) : Prop :=
  (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, TC.PtOf k q) ∧
    ∀ P ∈ I.SQ, P ∉ I.Q a → k.1.map (adAt B.host.F P) = 1

end BO

def StepCh {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) : Prop :=
  ∃ (C : Type) (_ : Fintype C) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (chOf : (I.stp u a i).Cl → C)
    (K : ∀ (hi : i ≤ B.R.m) (β : C), LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : C → TC.GA B (B.R.N i)),
    (∀ hi : i ≤ B.R.m, I.Reads u a i chOf (fun β => (K hi β).lev.Lb) (fun β => (K hi β).lev.U) (fun β => (K hi β).lev.chi)
      (fun c => ((K hi (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K hi (chOf c)).stabI ⟨c, rfl⟩ s).1) k) ∧
    (∀ hi : i ≤ B.R.m, ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K hi β).lev.chi κ ^ n = 1) ∧ (i ≤ B.R.m → ∀ β, BaseOk I u a i (k β)) ∧
    (i ≤ B.R.m → ∀ v ∈ bad, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v) ∧
    (i = B.R.m → Nonempty (Unique C)) ∧ (∀ h : i = B.R.m, ∀ β, I.TopPt l Z u a (h ▸ k β)) ∧ (i < B.R.m → ∀ β, k β = TC.kStd X u (B.R.N i))

section S0
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.Col2.MemChart GlobalTheory.Mem.Col2.TC.Chart0
attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 2000000 in

theorem stepCh_zero {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) : StepCh I l Z u a 0 := by
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  obtain ⟨hg, -, hl⟩ := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 0 hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u I.mu0).card_ST
  have hL := hI.idx_ok a
  let chOf : (I.stp u a 0).Cl → Unit := fun _ => ()
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := chart_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N 0)
    (fun w => (colLev I.Ch 0 w).H) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = B.T u)) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N 0) hPr u) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)
    (gramN (I.rec7 l Z) 0 hi) hg (badG (I.rec7 l Z)) (Set.ext fun v => (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm)
    (fun c : {c // chOf c = ()} => (I.stp u a 0).Stab c.1) (fun c => latCrd (I.rec7 l Z) 0 hi (I.latAt u a 0 c.1))
    (diaT (Pr := B.primes X) u) (fun c => ((I.stp u a 0).rep c.1).1.1.deco) (fun c => yT I u a c.1)
    (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).1) (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).2)
    ((stepZero_classes_bijective_decoratedLattice I hI u a).comp (Equiv.subtypeUnivEquiv fun _ => rfl).bijective) (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a) (lvQ I a) _ _ c.1) (fun c => stM_inj (lvG I a) (lvQ I a) _ _ ((l.ch u a).step 0) c.1)
    (fun c γ => stab_range0 I hI u a c.1 γ)
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N 0)
  letI := StepZero.idxUnique hL
  obtain ⟨q₀, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := 0) (DecoF.base _ _ _ _ _)
  have hm := B.R.two_le_m
  refine ⟨Unit, inferInstance, badG (I.rec7 l Z), chOf, fun _ _ => ⟨lev, Y, h1, h2, SI, h3, h4⟩, fun _ => kStd X u (B.R.N 0),
    fun _ => ⟨fun c c' => ⟨fun _ => ⟨Subsingleton.elim _ _, cos0 I _ _⟩, fun _ => rfl⟩,
      fun _ => ⟨(I.stp u a 0).cl default q₀, rfl⟩, fun β x => ?_, fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3,
      fun c => ?_, fun c x q h => ?_, fun c x κ hκ h => ?_, fun c s => h9 _ _⟩, fun _ _ => ?_,
    fun _ _ => ⟨kStd_pt I hI u a 0, fun P hP _ => kStd_at_SQ I hI u _ P hP⟩, fun _ v hv => Or.inl hv, fun h => absurd h (by omega),
    fun h => absurd h (by omega), fun _ _ => rfl⟩
  · exact (h5 ▸ Iff.rfl : x ∈ lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u)).trans (mem_baseLb hPr u _ x)
  · have e := h8 ⟨c, rfl⟩
    show PtOf ((Y ⟨c, rfl⟩).1 * kStd X u (B.R.N 0)) _
    rw [e]
    exact yT_spec I hI u a c
  · have e := h8 ⟨c, rfl⟩
    replace h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q := e ▸ h
    exact (h6 ▸ Iff.rfl : x ∈ lev.U ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp).trans (lev0 I hI hPr u a c x q h)
  · have e := h8 ⟨c, rfl⟩
    have hx : (id x.1 : GA B (B.R.N 0)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp := h6 ▸ x.2
    refine (congrArg Units.val (h7 x hx)).trans ?_
    exact chr0 I hI hPr u a c x.1 hx κ hκ (e ▸ h)
  · obtain ⟨m, hm, hc⟩ := GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp (colLev I.Ch 0)
    refine ⟨m, hm, fun κ => ?_⟩
    show lev.chi κ ^ m = 1
    have hx : (id κ.1 : GA B (B.R.N 0)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp := h6 ▸ κ.2
    have e1 : ∀ z, (((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) z) ^ m = 1 := fun z => by
      rw [← map_pow]
      show Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (z ^ m)) = 1
      rw [map_pow, hc, map_one]
    rw [h7 κ hx, levTyp, MonoidHom.inv_apply, inv_pow, levChr, MonoidHom.comp_apply]
    exact (congrArg (fun t => t⁻¹) (e1 _)).trans inv_one

end S0

theorem topBaseOk {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) {C : Type} (chOf : (I.stp u a B.R.m).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E))
    (U : C → Subgroup (TC.GA B (B.R.N B.R.m))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a B.R.m).Cl → TC.GA B (B.R.N B.R.m))
    (st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E) (k : C → TC.GA B (B.R.N B.R.m))
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k) (htop : ∀ β, I.TopPt l Z u a (k β)) (β : C) : BaseOk I u a B.R.m (k β) := by
  exact GlobalTheory.T.lastStepChartBasePoint_carries_stdPoint I hI hP l Z u a chOf Lb U chi y st k hR htop β

section SMid
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.Col2.MemChart
attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 2000000 in

theorem stepCh_mid {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < B.R.m) : StepCh I l Z u a i := by
  classical
  have hPr := l.pr
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := fun v => Finset.mem_image
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N i)
  have hk : GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun _ : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i => kStd X u (B.R.N i)) :=
    ⟨fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3⟩
  obtain ⟨K, hK, hfin⟩ := GlobalTheory.Mem.Col2.ChExM.exists_charts I hI hP l Z u a Q i h2.le h1 h2 hQ _ hk
  haveI := GlobalTheory.Mem.Col2.TC.ChTw.finite_chart I l u a i
  exact ⟨GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, Fintype.ofFinite _, badQ (I.rec7 l Z) Q, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i,
    fun _ => K, fun _ => kStd X u (B.R.N i), fun _ => hK, fun _ => hfin,
    fun _ _ => ⟨kStd_pt I hI u a i, fun P hP _ => kStd_at_SQ I hI u _ P hP⟩,
    fun _ v hv => hv.imp id (hQ v).1, fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ _ => rfl⟩

set_option maxHeartbeats 2000000 in

theorem stepCh_top {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) : StepCh I l Z u a B.R.m := by
  classical
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := fun v => Finset.mem_image
  obtain ⟨Ch0, _, chOf0, K0, h1, -, h3⟩ := GlobalTheory.Mem.Col2.MemChart.exists_charts I hI hP l Z u B.R.m le_rfl
  let β0 : Ch0 := (h3 (Or.inr rfl)).some.default
  have hβ0 : ∀ c, chOf0 c = β0 := fun c => (h3 (Or.inr rfl)).some.uniq _
  obtain ⟨K1, ⟨k, hk, htop⟩, -, -, hfin, -⟩ := GlobalTheory.Mem.Col2.TC.chart_twm I hI hP l Z u a Q
    (GlobalTheory.Mem.FormSym.clsOfChart β0 hβ0 (K0 β0)) hQ (GlobalTheory.Mem.FormSym.readsK_one I l Z h1 β0 hβ0)
  have hm := B.R.two_le_m
  exact ⟨Unit, inferInstance, badQ (I.rec7 l Z) Q, fun _ => (), fun _ => K1, k, fun _ => hk, fun _ _ => hfin,
    fun _ β => topBaseOk I hI hP l Z u a _ _ _ _ _ _ k hk htop β,
    fun _ v hv => hv.imp id (hQ v).1, fun _ => ⟨inferInstance⟩,
    fun h β => by
      show I.TopPt l Z u a (k β)
      exact htop β, fun h => absurd h (lt_irrefl _)⟩

theorem stepCh_above {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : B.R.m < i) : StepCh I l Z u a i := by
  classical
  have h := (l.ch u a).step i
  haveI : Finite (I.stp u a i).Cl := @Finite.instSigma _ _ inferInstance h.fin_orb
  exact ⟨(I.stp u a i).Cl, Fintype.ofFinite _, ∅, id, fun h' => absurd h' (by omega), fun _ => 1,
    fun h' => absurd h' (by omega), fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
    fun h' => absurd h' (by omega), fun h' => absurd h' (by omega), fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩

theorem stepCh_all {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) : StepCh I l Z u a i := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact stepCh_zero I hI hP l Z u a
  rcases lt_trichotomy i B.R.m with h | rfl | h
  · exact stepCh_mid I hI hP l Z u a i hpos h
  · exact stepCh_top I hI hP l Z u a
  · exact stepCh_above I l Z u a i h

end SMid

theorem liftKA {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (i : ℕ) (hi : i ≤ B.R.m) (k : TC.GA B (B.R.N i))
    (hk : ∃ p : Formalism.L2.Col.DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, TC.PtOf k p ∧ p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) :
    ∃ kA : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i), kA ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) kA = k.1 :=
  GlobalTheory.T.exists_adelicUnitaryLift_of_chartBasePoint I hI hP l Z i hi k hk

theorem levData {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m)
    {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} (K : LevelChart (I.rec7 l Z) T bad i hi stab lat) :
    ∃ (U : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))) (chi : U →* ℂˣ) (h : cl → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)),
      (∀ g, g ∈ U ↔ g ∈ GfC _ ∧ ∃ κ : K.lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧
      (∀ (g : U) (κ : K.lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi g = K.lev.chi κ) ∧
      (∀ c, h c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h c) = (K.y c).1.1) :=
  GlobalTheory.T.chartLevelCharacterReps_on_adelicUnitaryPoints I l Z i hi K

theorem pointOf {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ)
    (hi : i ≤ B.R.m) {C : Type} (chOf : (I.stp u a i).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E))
    (U : C → Subgroup (TC.GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → TC.GA B (B.R.N i))
    (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : C → TC.GA B (B.R.N i))
    (hR : I.Reads u a i chOf Lb U chi y st k) (β : C) (hb : BaseOk I u a i (k β)) :
    ∃ (b0 : Idx I.sel (I.tup a) (I.idx a) i) (p0 : PtAt B.R I.sel (I.tup a) (I.cst a) u i),
      TC.PtOf (k β) (extTo I.SQ p0.1.1) ∧ p0.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) ∧
      ∀ c, chOf c = β → c.1 = b0 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn p0 :=
  GlobalTheory.T.exists_stepPoint_of_chartBasePoint I hI hP u a i hi chOf Lb U chi y st k hR β hb.1 hb.2

set_option maxHeartbeats 2000000 in

theorem comp {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {C : Type} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} (chOf : (I.stp u a i).Cl → C)
    (K : ∀ β : C, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : C → TC.GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k) (hb : ∀ β, BaseOk I u a i (k β)) :
    ∃ (kA : C → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (xr : C → (AE (I.rec7 l Z))ˣ) (b0 : C → Idx I.sel (I.tup a) (I.idx a) i)
      (p0 : C → PtAt B.R I.sel (I.tup a) (I.cst a) u i) (U : C → Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)))
      (chi : ∀ β, U β →* ℂˣ) (h : ∀ β : C, {c // chOf c = β} → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)),
      (∀ β, kA β ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (kA β) = (k β).1 ∧ IsDetRoot _ (kA β) (xr β)) ∧
      (∀ β, TC.PtOf (k β) (extTo I.SQ (p0 β).1.1) ∧ (p0 β).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) ∧
      (∀ c, c.1 = b0 (chOf c) ∧ cosetIn ((I.stp u a i).rep c) = cosetIn (p0 (chOf c))) ∧
      (∀ β g, g ∈ U β ↔ g ∈ GfC _ ∧ ∃ κ : (K β).lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧
      (∀ β (g : U β) (κ : (K β).lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi β g = (K β).lev.chi κ) ∧
      (∀ β c, h β c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h β c) = ((K β).y c).1.1) := by
  choose kA hkA using fun β => liftKA I hI hP l Z i hi (k β) (hR.k_std β)
  choose xr hxr using fun β => GlobalTheory.RecDict.exists_isDetRoot (I.rec7 l Z) _ (kA β)
  choose b0 p0 hp1 hp2 hp3 using fun β => pointOf I hI hP l u a i hi chOf _ _ _ _ _ k hR β (hb β)
  choose U chi h hU hchi hh using fun β => levData I l Z i hi (K β)
  exact ⟨kA, xr, b0, p0, U, chi, h, fun β => ⟨(hkA β).1, (hkA β).2, hxr β⟩, fun β => ⟨hp1 β, hp2 β⟩,
    fun c => hp3 (chOf c) c rfl, hU, hchi, hh⟩

def FullStep {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) : Prop :=
  ∃ (C : Type) (_ : Fintype C) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (chOf : (I.stp u a i).Cl → C)
    (K : ∀ (hi : i ≤ B.R.m) (β : C), LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : C → TC.GA B (B.R.N i))
    (kA : C → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (xr : C → (AE (I.rec7 l Z))ˣ) (b0 : C → Idx I.sel (I.tup a) (I.idx a) i)
    (p0 : C → PtAt B.R I.sel (I.tup a) (I.cst a) u i) (U : C → Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)))
    (chi : ∀ β, U β →* ℂˣ) (h : ∀ β : C, {c // chOf c = β} → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)),
    (∀ hi : i ≤ B.R.m, I.Reads u a i chOf (fun β => (K hi β).lev.Lb) (fun β => (K hi β).lev.U) (fun β => (K hi β).lev.chi)
      (fun c => ((K hi (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K hi (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      (∀ β, kA β ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (kA β) = (k β).1 ∧ IsDetRoot _ (kA β) (xr β)) ∧
      (∀ β, TC.PtOf (k β) (extTo I.SQ (p0 β).1.1) ∧ (p0 β).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) ∧
      (∀ c, c.1 = b0 (chOf c) ∧ cosetIn ((I.stp u a i).rep c) = cosetIn (p0 (chOf c))) ∧
      (∀ β g, g ∈ U β ↔ g ∈ GfC _ ∧ ∃ κ : (K hi β).lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧
      (∀ β (g : U β) (κ : (K hi β).lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi β g = (K hi β).lev.chi κ) ∧
      (∀ β c, h β c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h β c) = ((K hi β).y c).1.1) ∧
      (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K hi β).lev.chi κ ^ n = 1) ∧ (∀ v ∈ bad, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v)) ∧
    (i = B.R.m → Nonempty (Unique C)) ∧ (∀ e : i = B.R.m, ∀ β, I.TopPt l Z u a (e ▸ k β)) ∧ (i < B.R.m → ∀ β, k β = TC.kStd X u (B.R.N i))

theorem fullStep {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (i : ℕ) : FullStep I l Z u a i := by
  classical
  by_cases hi : i ≤ B.R.m
  · obtain ⟨C, hC, bad, chOf, K, k, hR, hF, hBO, hB, hU, hT, hS⟩ := stepCh_all I hI hP l Z u a i
    obtain ⟨kA, xr, b0, p0, U, chi, h, c1, c2, c3, c4, c5, c6⟩ := comp I hI hP l Z u a i hi chOf (K hi) k (hR hi) (hBO hi)
    exact ⟨C, hC, bad, chOf, K, k, kA, xr, b0, p0, U, chi, h, fun hi' => ⟨hR hi', c1, c2, c3, c4, c5, c6, hF hi', hB hi'⟩, hU, hT, hS⟩
  · have h' := (l.ch u a).step i
    haveI : Finite (I.stp u a i).Cl := @Finite.instSigma _ _ inferInstance h'.fin_orb
    exact ⟨(I.stp u a i).Cl, Fintype.ofFinite _, ∅, id, fun h' => absurd h' hi, fun _ => 1, fun _ => 1, fun _ => 1, fun c => c.1,
      fun c => (I.stp u a i).rep c, fun _ => ⊥, fun _ => 1, fun _ _ => 1, fun h' => absurd h' hi, fun h' => absurd h' (by omega),
      fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩

theorem exists_chr {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) :
    ∃ chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle), ∀ j : Fin B.R.m, ChrEq (chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) := by
  have hc : ∀ j : ℕ, ∃ c : (AE (I.rec7 l Z))ˣ →* Circle, ∀ h : j - 1 < B.R.m, 1 ≤ j → ChrEq c (I.C.mu0 ⟨j - 1, h⟩ * I.xi a) := by
    intro j
    by_cases h : j - 1 < B.R.m
    · obtain ⟨c, hc⟩ := GlobalTheory.CharTransport.exists_chrEq (I.rec7 l Z) (I.C.mu0 ⟨j - 1, h⟩ * I.xi a)
        ((I.C.isMu0 _).unitary.mul (GlobalTheory.Mem.Col2.ColIn.Ok.xi_unitary hI a))
      exact ⟨c, fun _ _ => hc⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose chr hchr using hc
  exact ⟨chr, fun j => hchr ((j : ℕ) + 1) (by simp) (by omega)⟩

theorem exists_idem {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    ∃ e : AE (I.rec7 l Z), IsIdemSum e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr hI.sel_ok
    (hI.T_mem u) hI.g_mem
  refine GlobalTheory.MuLift.exists_idemSum _ fun Q hQ Q' hQ' hc => ?_
  have h1 : Q' = Formalism.DivisionValues.conjPl Q := GlobalTheory.GoodPrimes.isConjPl_iff.1 hc
  have h2 := (bad Q hQ).1
  have h3 : Formalism.L2.Col.conjPrime₂ Q = Q' := (GlobalTheory.PlaceDict.conjP_eq_conjPl (I.rec7 l Z) Q).trans h1.symm
  have h4 : @Formalism.L2.Col.conjPrime₂ B.fields.E B.fields.fieldE _ B.fields.starE Q = Q' := h3
  exact h2 (h4 ▸ hQ')

end GlobalTheory.AdForm.TupEx

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.AdForm.exists_twDat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (Ch : ℕ → Type) (_ : ∀ i, Fintype (Ch i)) (A : TwDat I l Z u a Ch), A.Is ∧ Nonempty (Unique (Ch B.R.m)) ∧ ∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i) := by
  intro B X I hI hP l Z u a
  choose C hC bad chOf K k kA xr b0 p0 U chi h hS hU hT hStd using fun i => GlobalTheory.AdForm.TupEx.fullStep I hI hP l Z u a i
  obtain ⟨chr, hchr⟩ := GlobalTheory.AdForm.TupEx.exists_chr I hI l Z a
  obtain ⟨e, he⟩ := GlobalTheory.AdForm.TupEx.exists_idem I hI l Z u a
  refine ⟨C, hC, ⟨bad, chOf, K, k, kA, xr, b0, p0, U, chi, h, chr, e⟩,
    ⟨fun i hi => (hS i hi).1, fun β => hT B.R.m rfl β, fun i hi β => (hS i hi).2.1 β,
      fun i hi β => (hS i hi).2.2.1 β, fun i hi c => (hS i hi).2.2.2.1 c, fun i hi β g => (hS i hi).2.2.2.2.1 β g,
      fun i hi β g κ hκ => (hS i hi).2.2.2.2.2.1 β g κ hκ, fun i hi β c => (hS i hi).2.2.2.2.2.2.1 β c, hchr, he,
      fun i hi β => (hS i hi).2.2.2.2.2.2.2.1 β, fun i hi v hv => (hS i hi).2.2.2.2.2.2.2.2 v hv⟩,
    hU B.R.m rfl, fun i hi β => hStd i hi β⟩
