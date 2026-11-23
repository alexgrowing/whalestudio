import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Formalism.LocalToGlobal.HermitianForms.TiedTwSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartsTupleTrivQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnChartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTupleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepQOfReindex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPenultimateLevelCouplingCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlacesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct
section
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

set_option maxHeartbeats 4000000 in

structure TwStep (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (u : B.Word) (a : I.ι) (i : ℕ) where
  Ch : Type
  fin : Finite Ch
  chOf : (I.stp u a i).Cl → Ch
  gOf : Ch → H.Ch u i
  K : ∀ (_ : 1 ≤ i) (hm : i ≤ B.R.m) (β : Ch), LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hm
    (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hm (I.latAt u a i c.1))
  reads : ∀ h1 hm, I.ReadsK l Z u a i hm chOf (K h1 hm)
  readsQ : ∀ h1 hm, i + 1 ≤ B.R.m → ∃ k : Ch → GA B (B.R.N i), I.Reads u a i chOf (fun β => (K h1 hm β).lev.Lb) (fun β => (K h1 hm β).lev.U)
    (fun β => (K h1 hm β).lev.chi) (fun c => ((K h1 hm (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K h1 hm (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1
  fk : ∀ h1 hm β, FunKilled (K h1 hm β).lev (X.piT u)
  lev : ∀ (_ : 1 ≤ i) (_ : i ≤ B.R.m) (_ : Ch),
    Formalism.L2.Herm.StepLevelQ (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g (B.T u) B.R.f Q
  cls : ∀ h1 hm β, Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (lev h1 hm β).Lb (lev h1 hm β).U
    (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => I.latAt u a i c.1)
  car : ∀ h1 hm β, SameCar (rankN (I.rec7 l Z) i hm) (lev h1 hm β).Lb (K h1 hm β).lev.Lb (lev h1 hm β).Uloc (K h1 hm β).lev.Uloc
    (lev h1 hm β).U (K h1 hm β).lev.U (fun c => ((cls h1 hm β).y c).1) (fun c => ((K h1 hm β).y c).1)
    (fun c s => ((cls h1 hm β).stabI c s).1) (fun c s => ((K h1 hm β).stabI c s).1)
  offU : ∀ h1 hm β v, v ∉ Q → (lev h1 hm β).Uloc v = (H.lev u i h1 hm (gOf β)).Uloc v
  offL : ∀ h1 hm β, (lev h1 hm β).Lb = (H.lev u i h1 hm (gOf β)).Lb
  offK : ∀ h1 (h2 : i + 1 ≤ B.R.m) β v, v ∉ Q → (K h1 (le_of_succ_m h2) β).lev.Uloc v = ((F u).ch i h1 h2 (gOf β)).lev.Uloc v
  uniq : i = B.R.m → Nonempty (Unique Ch)
  chiFin : a ≠ I.mu0 → ∀ h1 hm β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K h1 hm β).lev.chi κ ^ n = 1
  chiC : ∀ h1 (h2 : i + 1 ≤ B.R.m) β (κ : (K h1 (le_of_succ_m h2) β).lev.U) (κ' : ((F u).ch i h1 h2 (gOf β)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K h1 (le_of_succ_m h2) β).lev.chi κ = ((F u).ch i h1 h2 (gOf β)).lev.chi κ'

variable {I l Z}

theorem twStep_out {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι) (i : ℕ) (hout : ¬ (1 ≤ i ∧ i ≤ B.R.m))
    (f : (I.stp u a i).Cl → H.Ch u i) : Nonempty (TwStep I l Z H F Q u a i) :=
  ⟨{ Ch := H.Ch u i
     fin := H.ChFin u i
     chOf := f
     gOf := id
     K := fun h1 hm => absurd ⟨h1, hm⟩ hout
     reads := fun h1 hm => absurd ⟨h1, hm⟩ hout
     readsQ := fun h1 hm => absurd ⟨h1, hm⟩ hout
     fk := fun h1 hm => absurd ⟨h1, hm⟩ hout
     lev := fun h1 hm => absurd ⟨h1, hm⟩ hout
     cls := fun h1 hm => absurd ⟨h1, hm⟩ hout
     car := fun h1 hm => absurd ⟨h1, hm⟩ hout
     offU := fun h1 hm => absurd ⟨h1, hm⟩ hout
     offL := fun h1 hm => absurd ⟨h1, hm⟩ hout
     offK := fun h1 h2 => absurd ⟨h1, le_of_succ_m h2⟩ hout
     uniq := fun e => absurd ⟨by have := B.R.two_le_m; omega, by omega⟩ hout
     chiFin := fun _ h1 hm => absurd ⟨h1, hm⟩ hout
     chiC := fun h1 h2 => absurd ⟨h1, le_of_succ_m h2⟩ hout }⟩

theorem swap_ex (hok : I.Ok) (pins : TC.Pins B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)))
    (hK : I.ReadsK l Z u a i hi chOf K) (β : Ch) :
    ∃ Kr, ∃ hl : GlobalTheory.Mem.Col2.Reside.SwapLaws (K β).lev Kr, FunKilled (GlobalTheory.Mem.Col2.Reside.swap (K β).lev Kr hl) (X.piT u) := by
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hok pins l Z
  obtain ⟨hgr, -, -⟩ := hc i hi
  have hB := basePi_of_ok hX hPr u
  have hLb : (K β).lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) := by
    obtain ⟨k, hk⟩ := hK
    ext x
    exact (hk.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  exact ⟨_, GlobalTheory.Mem.Col2.Reside.swapLaws B.sp.cm hB (hPr.T_prime u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => hPr.vT_norm u P hP) hgr (K β).lev hLb⟩

def killK (hok : I.Ok) (pins : TC.Pins B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)))
    (hK : I.ReadsK l Z u a i hi chOf K) (β : Ch) :
    LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)) :=
  { K β with lev := GlobalTheory.Mem.Col2.Reside.swap (K β).lev _ (swap_ex hok pins u a i hi K hK β).choose_spec.choose }

def twStep_mk (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι) (i : ℕ) (h1i : 1 ≤ i) (hmi : i ≤ B.R.m)
    (hQ : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal)
    (Ch : Type) (fin : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (g : Ch → H.Ch u i)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hmi
      (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hmi (I.latAt u a i c.1)))
    (hr : I.ReadsK l Z u a i hmi chOf K)
    (hrQ : i + 1 ≤ B.R.m → ∃ k : Ch → GA B (B.R.N i), I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U)
    (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1)
    (hLb : ∀ β, (K β).lev.Lb = reL (rankN (I.rec7 l Z) i hmi) (H.lev u i h1i hmi (g β)).Lb)
    (hU : ∀ β v, v ∉ Q → (K β).lev.Uloc v = ((H.lev u i h1i hmi (g β)).Uloc v).map (reGL (rankN (I.rec7 l Z) i hmi) _).toMonoidHom)
    (hK : ∀ h1 (h2 : i + 1 ≤ B.R.m) β v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch i h1 h2 (g β)).lev.Uloc v)
    (hu : i = B.R.m → Nonempty (Unique Ch))
    (hF : a ≠ I.mu0 → ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1)
    (hC : ∀ h1 (h2 : i + 1 ≤ B.R.m) β (κ : (K β).lev.U) (κ' : ((F u).ch i h1 h2 (g β)).lev.U), κ.1 = κ'.1 →
      (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch i h1 h2 (g β)).lev.chi κ') :
    TwStep I l Z H F Q u a i :=
  have hx := fun β => GlobalTheory.ChartQ.chartTie_toQ Q hmi _ _ (killK hok pins u a i hmi K hr β) (H.lev u i h1i hmi (g β)) hQ (hLb β) (hU β)
  { Ch := Ch, fin := fin, chOf := chOf, gOf := g, K := fun _ _ => killK hok pins u a i hmi K hr, reads := fun _ _ => hr, readsQ := fun _ _ => hrQ,
    fk := fun _ _ β => (swap_ex hok pins u a i hmi K hr β).choose_spec.choose_spec, lev := fun _ _ β => (hx β).choose,
    cls := fun _ _ β => (hx β).choose_spec.choose, car := fun _ _ β => (hx β).choose_spec.choose_spec.2,
    offU := fun _ _ β v hv => by
      have h1 : (K β).lev.Uloc v = _ := (hx β).choose_spec.choose_spec.2.Uloc_eq v
      rw [hU β v hv] at h1
      exact Subgroup.map_injective (reGL (rankN (I.rec7 l Z) i hmi) _).injective h1.symm,
    offL := fun _ _ β => (hx β).choose_spec.choose_spec.1, offK := hK, uniq := hu,
    chiFin := fun h _ _ => hF h, chiC := hC }

theorem reads_lb_eq {u : B.Word} {a a' : I.ι} {i : ℕ} {hi : i ≤ B.R.m} {bad bad' : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch Ch' : Type}
    {chOf : (I.stp u a i).Cl → Ch} {chOf' : (I.stp u a' i).Cl → Ch'}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))}
    {K' : ∀ β : Ch', LevelChart (I.rec7 l Z) (B.T u) bad' i hi (fun c : {c // chOf' c = β} => (I.chain l u a').stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a' i c.1))}
    (h : I.ReadsK l Z u a i hi chOf K) (h' : I.ReadsK l Z u a' i hi chOf' K') (β : Ch) (β' : Ch') :
    (K β).lev.Lb = (K' β').lev.Lb := by
  obtain ⟨k, R⟩ := h
  obtain ⟨k', R'⟩ := h'
  ext x
  exact (R.lb β x).trans (R'.lb β' x).symm

theorem twStep_mid (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ B.R.m)
    (hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v)
    (hF : ∀ u, I.StdF l Z u (F u)) (hC : CarH H F) : Nonempty (TwStep I l Z H F Q u a i) := by
  have hoff : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal :=
    fun v hv => GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes I hok l u a v ((hQ v).1 hv)
  have hi : i ≤ B.R.m := le_of_succ_m h2
  by_cases ha : a = I.mu0
  · subst ha
    have hr0 := (hF u).mid i h1 h2
    let K : ∀ β : H.Ch u i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi
        (fun c : {c // H.chOf u i c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1)) :=
      fun β => chartWiden Set.subset_union_left ((F u).ch i h1 h2 β)
    refine ⟨twStep_mk hok pins u I.mu0 i h1 hi hoff (H.Ch u i) (H.ChFin u i) (H.chOf u i) id K hr0
      (fun _ => hr0.elim fun k hk => ⟨k, hk, fun _ v hv => absurd hv (GlobalTheory.T.not_twistPlace_referenceTuple I hok v)⟩) (fun β => ?_) (fun β v _ => ?_) (fun _ _ β v _ => rfl)
      (fun e => by omega) (fun h => absurd rfl h) (fun _ _ β κ κ' e _ => ?_)⟩
    · exact (hC.carC u i h1 h2 β).Lb_eq
    · exact (hC.carC u i h1 h2 β).Uloc_eq v
    · have : κ = κ' := Subtype.ext e
      subst this
      rfl
  · obtain ⟨Ch, fin, chOf, K, g, hrQ, hp⟩ := GlobalTheory.Mem.Col2.TC.ChTw.charts_tuple_trivQ I hok pins l Z u a Q i hi (H.Ch u i) (H.chOf u i) ((F u).ch i h1 h2) h1 (by omega) hQ
      ((hF u).mid i h1 h2)
    have hr : I.ReadsK l Z u a i hi chOf K := hrQ.elim fun k hk => ⟨k, hk.1⟩
    have hoU : ∀ β v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch i h1 h2 (g β)).lev.Uloc v := fun β v hv => (hp β).1 v hv
    refine ⟨twStep_mk hok pins u a i h1 hi hoff Ch fin chOf g K hr (fun _ => hrQ) (fun β => ?_) (fun β v hv => ?_) (fun _ _ β v hv => hoU β v hv)
      (fun e => by omega) (fun _ β => (hp β).2.1) (fun _ _ β κ κ' e hv => (hp β).2.2 κ κ' e hv)⟩
    · rw [reads_lb_eq hr ((hF u).mid i h1 h2) β (g β)]
      exact (hC.carC u i h1 h2 (g β)).Lb_eq
    · rw [hoU β v hv]
      exact (hC.carC u i h1 h2 (g β)).Uloc_eq v

structure TopP {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} {u : B.Word} {a : I.ι} (S : TwStep I l Z H F Q u a B.R.m) : Prop where
  chiM : ∀ h1 β (κ : (S.K h1 le_rfl β).lev.U) (κ' : ((F u).cls B.R.m le_rfl (Or.inr rfl)).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (S.K h1 le_rfl β).lev.chi κ = ((F u).cls B.R.m le_rfl (Or.inr rfl)).lev.chi κ'
  top : a ≠ I.mu0 → ∀ h1 β, I.TopBase l Z u a (S.K h1 le_rfl β).lev.U fun c => ((S.K h1 le_rfl (S.chOf c)).y ⟨c, rfl⟩).1
  topk : a ≠ I.mu0 → ∀ h1, ∃ k, I.Reads u a B.R.m S.chOf (fun β => (S.K h1 le_rfl β).lev.Lb) (fun β => (S.K h1 le_rfl β).lev.U)
    (fun β => (S.K h1 le_rfl β).lev.chi) (fun c => ((S.K h1 le_rfl (S.chOf c)).y ⟨c, rfl⟩).1)
    (fun c s => ((S.K h1 le_rfl (S.chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)

theorem twStep_top (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι)
    (hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v)
    (hF : ∀ u, I.StdF l Z u (F u)) (hC : CarH H F) : ∃ S : TwStep I l Z H F Q u a B.R.m, TopP S := by
  have hoff : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal :=
    fun v hv => GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes I hok l u a v ((hQ v).1 hv)
  have h1m : 1 ≤ B.R.m := one_le_m B.R
  have hr0 := (hF u).ends B.R.m le_rfl (Or.inr rfl)
  have hno : ∀ h2 : B.R.m + 1 ≤ B.R.m, False := fun h2 => by omega
  by_cases ha : a = I.mu0
  · subst ha
    let K : ∀ β : Unit, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) B.R.m le_rfl
        (fun c : {c // (fun _ : (I.stp u I.mu0 B.R.m).Cl => ()) c = β} => (I.chain l u I.mu0).stab B.R.m c.1)
        (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u I.mu0 B.R.m c.1)) :=
      chartAll (chartWiden Set.subset_union_left ((F u).cls B.R.m le_rfl (Or.inr rfl)).toChart)
    have hr : I.ReadsK l Z u I.mu0 B.R.m le_rfl (fun _ => ()) K := hr0
    refine ⟨twStep_mk hok pins u I.mu0 B.R.m h1m le_rfl hoff Unit inferInstance (fun _ => ()) (fun _ => chM H u) K hr (fun h2 => (hno h2).elim) (fun β => ?_) (fun β v _ => ?_)
      (fun _ h2 => (hno h2).elim) (fun _ => ⟨inferInstance⟩) (fun h => absurd rfl h) (fun _ h2 => (hno h2).elim), ?_, ?_, ?_⟩
    · exact (hC.carM u).Lb_eq
    · exact (hC.carM u).Uloc_eq v
    · intro _ β κ κ' e _
      have : κ = κ' := Subtype.ext e
      subst this
      rfl
    · exact fun h => absurd rfl h
    · exact fun h => absurd rfl h
  · obtain ⟨K1, ⟨k1, hR1, hk1⟩, htop, hoU, hfin, hchi⟩ := GlobalTheory.T.chart_lastStep_twistBasePoint I hok pins l Z u a Q ((F u).cls B.R.m le_rfl (Or.inr rfl)) hQ hr0
    have hr : I.ReadsK l Z u a B.R.m le_rfl (fun _ => ()) K1 := ⟨k1, hR1⟩
    refine ⟨twStep_mk hok pins u a B.R.m h1m le_rfl hoff Unit inferInstance (fun _ => ()) (fun _ => chM H u) K1 hr (fun h2 => (hno h2).elim) (fun β => ?_) (fun β v hv => ?_)
      (fun _ h2 => (hno h2).elim) (fun _ => ⟨inferInstance⟩) (fun _ β => hfin) (fun _ h2 => (hno h2).elim), ?_, ?_, ?_⟩
    · have e0 : (K1 β).lev.Lb = ((F u).cls B.R.m le_rfl (Or.inr rfl)).lev.Lb := by
        obtain ⟨k, R⟩ := hr
        obtain ⟨k', R'⟩ := hr0
        ext x
        exact (R.lb β x).trans (R'.lb () x).symm
      rw [e0]
      exact (hC.carM u).Lb_eq
    · have : β = () := rfl
      subst this
      rw [hoU v hv]
      exact (hC.carM u).Uloc_eq v
    · intro _ β κ κ' e hv
      exact hchi κ κ' e hv
    · intro _ _ β
      exact htop
    · intro _ _
      exact ⟨k1, hR1, hk1⟩

set_option maxHeartbeats 8000000 in

structure TwPack (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (u : B.Word) (a : I.ι) where
  St : ∀ i, TwStep I l Z H F Q u a i
  top : TopP (St B.R.m)
  J : TwLevJ I l Z F Q u a (St (B.R.m - 1)).chOf (fun β => (St (B.R.m - 1)).K (by have := B.R.two_le_m; omega) (Nat.sub_le _ _) β)
  off : ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → J.chiJ κ = (F u).levJ.chi κ'

theorem twBefore_cl_nonempty (hOk : I.Ok) (u : B.Word) (a : I.ι) : Nonempty (I.stp u a (B.R.m - 1)).Cl := by
  classical
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  have hL := hOk.idx_ok a
  obtain ⟨b0x, -⟩ := hL.last_uniq
  let b0 : Idx I.sel (I.tup a) (I.idx a) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u a (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  exact ⟨(I.stp u a (B.R.m - 1)).cl b0 q0⟩

set_option maxHeartbeats 8000000 in
theorem twPack_ex (hok : I.Ok) (pins : TC.Pins B X) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (u : B.Word) (a : I.ι)
    (hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v) (hF : ∀ u, I.StdF l Z u (F u)) (hJ : ∀ u j v h, (F u).glevJ.fr j v h = 1) (hC : CarH H F) :
    Nonempty (TwPack (I := I) (l := l) (Z := Z) H F Q u a) := by
  have ex : ∀ i, Nonempty (TwStep I l Z H F Q u a i) := fun i => by
    by_cases h0 : i = 0
    · subst h0
      exact twStep_out u a 0 (by omega) (fun c => H.chOf u 0 ((I.eCls0 l u a).symm c))
    · by_cases h2 : i + 1 ≤ B.R.m
      · exact twStep_mid hok pins u a i (by omega) h2 hQ hF hC
      · by_cases h3 : i = B.R.m
        · subst h3
          exact (twStep_top hok pins u a hQ hF hC).elim fun S _ => ⟨S⟩
        · obtain ⟨f⟩ := GlobalTheory.T.nonempty_classMap_above_lastStep I hok u a i (by omega)
          exact twStep_out u a i (by omega) (fun c => H.chOf u i (f c))
  obtain ⟨Sm, hSm⟩ := twStep_top (F := F) (Q := Q) hok pins u a hQ hF hC
  let St : ∀ i, TwStep I l Z H F Q u a i := Function.update (fun i => (ex i).some) B.R.m Sm
  have hSt : St B.R.m = Sm := Function.update_self _ _ _
  have h1 : 1 ≤ B.R.m - 1 := by have := B.R.two_le_m; omega
  have h2 := succ_pred_m B.R
  have hfin : ∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev := fun β => by
    by_cases ha : a = I.mu0
    · refine ⟨1, one_pos, fun κ hκ => ?_⟩
      rw [pow_one]
      refine ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev.chi_triv κ fun v hv => ?_
      rcases hv with hv | hv
      · exact hκ v hv
      · exact absurd (ha ▸ (hQ v).1 hv) (GlobalTheory.T.not_twistPlace_referenceTuple I hok v)
    · obtain ⟨n, hn, h⟩ := (St (B.R.m - 1)).chiFin ha h1 (Nat.sub_le _ _) β
      exact ⟨n, hn, fun κ _ => h κ⟩
  obtain ⟨J⟩ := GlobalTheory.T.exists_penultimateLevel_couplingCosets I hok pins l Z H.Ch H.chOf F u a Q h1 (St (B.R.m - 1)).Ch (St (B.R.m - 1)).fin (St (B.R.m - 1)).chOf
    (fun β => (St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β) (St (B.R.m - 1)).gOf hQ hF hJ ((St (B.R.m - 1)).readsQ h1 (Nat.sub_le _ _) h2) hfin
    (fun β v hv => (St (B.R.m - 1)).offK h1 h2 β v hv) (fun β κ κ' e hv => (St (B.R.m - 1)).chiC h1 h2 β κ κ' e hv)
  have hLb : (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.levJ.Lb := by
    obtain ⟨c⟩ := twBefore_cl_nonempty hok u a
    rw [← J.lb ((St (B.R.m - 1)).chOf c), ← (F u).levJ_Lb h1 ((St (B.R.m - 1)).gOf ((St (B.R.m - 1)).chOf c))]
    exact (reads_lb_eq ((St (B.R.m - 1)).reads h1 (Nat.sub_le _ _)) ((hF u).mid (B.R.m - 1) h1 h2) _ _).symm
  have hoffx := GlobalTheory.T.exists_levelJ_character_eq_member_off_places I hok pins l Z H.Ch H.chOf F u a Q h1 (St (B.R.m - 1)).Ch (St (B.R.m - 1)).fin (St (B.R.m - 1)).chOf
    (fun β => (St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β) (St (B.R.m - 1)).gOf hQ hF hJ ((St (B.R.m - 1)).reads h1 (Nat.sub_le _ _))
    (fun β v hv => (St (B.R.m - 1)).offK h1 h2 β v hv) (fun β κ κ' e hv => (St (B.R.m - 1)).chiC h1 h2 β κ κ' e hv) J
  have fin : (∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev.U),
      κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → ((St (B.R.m - 1)).K h1 (Nat.sub_le _ _) β).lev.chi κ' = χ κ) ∧
      ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
        (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ') := by
    first | exact hoffx hLb | exact hoffx
  obtain ⟨χ, hχ, hχ'⟩ := fin
  exact ⟨⟨St, hSt ▸ hSm, { J with chiJ := χ, chiJ_eq := hχ }, hχ'⟩⟩

theorem reL_inj {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] {L L' : Submodule (𝓞 E) (Fin a → E)}
    (e : reL h L = reL h L') : L = L' :=
  Submodule.map_injective_of_injective (f := (reV h E : (Fin a → E) →ₗ[E] (Fin b → E)).restrictScalars (𝓞 E)) (reV h E).injective e

def stab0Equiv (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl) (c' : (I.stp u a 0).Cl) : (I.stp u I.mu0 0).Stab c ≃* (I.stp u a 0).Stab c' :=
  have h0 : Subsingleton ((I.stp u I.mu0 0).Stab c) := ⟨fun x y => Subtype.ext
    (((l.lev u I.mu0).free0 c.1 x.1 _ x.2).trans ((l.lev u I.mu0).free0 c.1 y.1 _ y.2).symm)⟩
  have h1 : Subsingleton ((I.stp u a 0).Stab c') := ⟨fun x y => Subtype.ext
    (((l.lev u a).free0 c'.1 x.1 _ x.2).trans ((l.lev u a).free0 c'.1 y.1 _ y.2).symm)⟩
  { toFun := fun _ => 1
    invFun := fun _ => 1
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    map_mul' := fun _ _ => Subsingleton.elim _ _ }

set_option maxHeartbeats 4000000 in

def twT {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ where
  eCls0 u μ := I.eCls0 l u μ
  eStab0 u μ c := stab0Equiv (l := l) u μ c _
  eY _ _ _ _ := Equiv.refl _
  de_eq _ _ _ _ _ _ := rfl
  twisted_character_eq u μ φ c y := by
    show φ ((I.eCls0 l u μ).symm (I.eCls0 l u μ c)) y = φ c y
    exact congrArg (fun c' => φ c' y) (Equiv.symm_apply_apply _ c)
  Q := Q
  Q_iff := hQ
  Ch u μ i := ((p u μ).St i).Ch
  ChFin u μ i := ((p u μ).St i).fin
  Ch_m u μ := ((p u μ).St B.R.m).uniq rfl
  chOf u μ i := ((p u μ).St i).chOf
  lev u μ i h1 hm β := ((p u μ).St i).lev h1 hm β
  lat u μ i := I.latAt u μ i
  cls u μ _ i h1 hm β := ((p u μ).St i).cls h1 hm β
  levJ u μ _ := (p u μ).J.levJ
  Yb u μ _ := (p u μ).J.Yb
  YbFin u μ _ := (p u μ).J.YbFin
  YbAct u μ _ := (p u μ).J.YbAct
  yb u μ _ := (p u μ).J.yb
  yb_orbit u μ _ := (p u μ).J.yb_orbit
  levJ_Lb u μ h β := by
    have e1 := (((p u μ).St (B.R.m - 1)).car h (Nat.sub_le _ _) β).Lb_eq
    have e2 := (p u μ).J.lb β
    rw [e1] at e2
    exact reL_inj _ e2
  levJ_le u μ h β := by
    have e1 := (((p u μ).St (B.R.m - 1)).car h (Nat.sub_le _ _) β).U_eq
    have e2 := (p u μ).J.le β
    rw [e1] at e2
    exact (Subgroup.map_le_map_iff_of_injective (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).injective).1 e2
  levJ_stab u μ h β κ := by
    have e1 := (((p u μ).St (B.R.m - 1)).car h (Nat.sub_le _ _) β).U_eq
    have e2 := (p u μ).J.stab β κ
    rw [e1] at e2
    exact (Subgroup.mem_map_iff_mem (f := (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)
      (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).injective).symm.trans e2
  DGam_one _ _ := rfl

set_option maxHeartbeats 4000000 in

def twJ {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a)
    (hoff : ∀ (u : B.Word) a, ∀ v ∈ Q a, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) :
    Formalism.L2.Herm.TwChJointS (twT Q hQ p) H where
  gOf u μ i := ((p u μ).St i).gOf
  Uloc_off := by
    intro u μ i h1 hm β v hv
    intros
    exact ((p u μ).St i).offU h1 hm β v hv
  Lb_off u μ i h1 hm β v hv := congrArg _ (((p u μ).St i).offL h1 hm β)
  Q_off u μ := hoff u μ

theorem idY_twYS {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)} (hF : ∀ u, I.StdF l Z u (F u))
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) (u : B.Word) (μ : I.ι) (i : ℕ)
    (hi : i ≤ B.R.m) : I.IdY l Z u μ i hi (twYS (twT Q hQ p) F u μ i hi) := by
  intro y
  have e : (I.rec7 l Z).R.m = B.R.m := rfl
  show (eYS (F u) i hi y).1 = y.1
  unfold eYS
  split_ifs with h
  · exact (hF u).eY i hi h y
  · exact (hF u).eYC i (by omega) (by omega) y

set_option maxHeartbeats 8000000 in

def twW (hok : I.Ok) (pins : TC.Pins B X) (l0 : I.Law0 l) {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)} (hF : ∀ u, I.StdF l Z u (F u))
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a)
    (hoff : ∀ (u : B.Word) a, ∀ v ∈ Q a, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal)
    (A : ∀ u a, TwAtT (I.tw l l0 Z) u a) (hA : ∀ u a, (A u a).eVT = Equiv.refl _) :
    TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) (twT Q hQ p) (twJ Q hQ p hoff) F := by
  refine'
    { atT := A
      ch u μ _ i h1 hm β := ((p u μ).St i).K h1 hm β
      car u μ _ i h1 hm β := ((p u μ).St i).car h1 hm β
      chi_fin u μ hμ i h1 hm β := ((p u μ).St i).chiFin hμ h1 hm β
      chi_offC u μ _ i h1 h2 β κ κ' e hv := ((p u μ).St i).chiC h1 h2 β κ κ' e hv
      chi_offM u μ _ h1 β κ κ' e hv := (p u μ).top.chiM h1 β κ κ' e hv
      chiJ u μ _ := (p u μ).J.chiJ
      chiJ_eq u μ _ _ β κ κ' e := (p u μ).J.chiJ_eq β κ κ' e
      val u μ _ i h1 hm := by
        have hv := GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hok pins l Z u μ i hm _ _ _ (fun β => ((p u μ).St i).K h1 hm β) (twYS (twT Q hQ p) F u μ i hm)
          (((p u μ).St i).reads h1 hm) (idY_twYS hF Q hQ p u μ i hm)
        exact ⟨hv.Fi, hv.rat, fun w _ => hv.lat w trivial⟩
      dil u μ _ i h1 hm := GlobalTheory.T.diamondOperators_on_charts I hok pins l Z u μ i hm _ _ _ (fun β => ((p u μ).St i).K h1 hm β) (twYS (twT Q hQ p) F u μ i hm)
        ((A u μ).eV (F u).atT) (((p u μ).St i).reads h1 hm) (((p u μ).St i).fk h1 hm) (idY_twYS hF Q hQ p u μ i hm) (by
          intro v
          show ((F u).atT.eV ((A u μ).eVT v)).1 = _
          rw [hA u μ]
          exact (hF u).eV v)
      ipV u μ i hi := (GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie I hok pins l Z u μ i hi _ (idY_twYS hF Q hQ p u μ i hi)).1
      norm u μ i hi := (GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie I hok pins l Z u μ i hi _ (idY_twYS hF Q hQ p u μ i hi)).2
      twisted_e0_at_mu0_eq_eMu0 u x := GlobalTheory.T.stepZeroFormsIdentification_referenceTuple_eq_self I hok l Z l0 u x, .. }
  all_goals
    intro u μ h κ κ' e hv
    exact (p u μ).off κ κ' e hv

def twJS {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}
    {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
    (Q : I.ι → Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (hQ : ∀ a v, v ∈ Q a ↔ inQ a v)
    (p : ∀ u a, TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) : SymmetricTwistedJointForms (twT Q hQ p) F where
  J_g u μ _ j v hv x hx := (p u μ).J.J_g j v hv x hx
  J_off u μ _ v hv hb := (p u μ).J.J_off v hv hb
  yG u μ _ := (p u μ).J.yG
  yG_smul u μ _ κ y j v hv := (p u μ).J.yG_smul κ y j v hv
  YQ u μ _ := (p u μ).J.YQ
  yQ u μ _ := (p u μ).J.yQ
  y_inj u μ _ := (p u μ).J.y_inj
  yQ_off u μ _ := (p u μ).J.yQ_off

end

set_option maxHeartbeats 8000000 in

theorem tw_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → (∀ u j v h, (F u).glevJ.fr j v h = 1) → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) := by
  intro B X I hok pins l Z l0 inQ H F hin hF hC hJ
  have hF' : ∀ u, I.StdF l Z u (F u) := fun u => (hF u).1
  classical
  have hQex : ∀ a, ∃ Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ∀ v, v ∈ Q ↔ I.UnderQ a v :=
    fun a => ⟨(I.Q a).image (fun P => P.under (𝓞 B.host.F)), fun v => Finset.mem_image⟩
  choose Q hQ using hQex
  have hQ' : ∀ a v, v ∈ Q a ↔ inQ a v := fun a v => (hQ a v).trans (hin a v).symm
  have P : ∀ u a, Nonempty (TwPack (I := I) (l := l) (Z := Z) H F (Q a) u a) := fun u a => twPack_ex hok pins u a (hQ a) hF' hJ hC
  let p := fun u a => (P u a).some
  choose A hA hA' using fun u a => GlobalTheory.Mem.Col2.TwAtStd.twAtT_exists I hok pins l Z l0 u a
  have hoff : ∀ (u : B.Word) a, ∀ v ∈ Q a, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, (((I.rec7 l Z).host.g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal :=
    fun u a v hv => GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes I hok l u a v ((hQ a v).1 hv)
  refine ⟨twT Q hQ' p, twJ Q hQ' p hoff, twW hok pins l0 hF' Q hQ' p hoff A hA, ⟨fun u i hi => Equiv.ext fun y => rfl,
    fun u => Equiv.ext fun c => GlobalTheory.T.eCls0_mu0_eq_self I hok l u c⟩, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, hA, ?_,
    fun u a _ i h1 hm => ((p u a).St i).reads h1 hm, fun u a ha h1 β => (p u a).top.top ha h1 β,
    fun u a ha h1 => (p u a).top.topk ha h1, fun u a _ i h1 hm β => ((p u a).St i).fk h1 hm β⟩, ⟨twJS Q hQ' p⟩⟩
  intro u a v r
  show ((A u a).eFv v).symm ((F u).atT.res ((A u a).eVT v) r) = _
  rw [(hF' u).res]
  exact ((A u a).eFv v).symm_apply_eq.2 (hA' u a v r).symm

set_option maxHeartbeats 8000000 in

theorem tw_chains_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) :=
  fun I hok pins l Z l0 inQ H F hin hF hC => tw_chains I hok pins l Z l0 inQ H F hin hF hC fun u => (hF u).2.2

end GlobalTheory.Mem.Col2.TC
end
