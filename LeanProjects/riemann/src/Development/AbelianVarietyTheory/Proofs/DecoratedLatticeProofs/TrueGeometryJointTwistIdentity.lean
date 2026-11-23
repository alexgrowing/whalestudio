import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticExtensionCharactersPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame

noncomputable section

section General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QVecJoin
open GlobalTheory.QVec GlobalTheory.LocMod.StepVec

theorem step_mid : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j, j + 1 < D.R.m → GlobalTheory.FinPl.Moves (c.V j) (B.b j) (B.Λ j) (v.N j) S → GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → B.b j ∈ GfC (c.V j) → B.b (j + 1) ∈ GfC (c.V (j + 1)) → IsSelfDualC _ (B.Λ j) → IsSelfDualC _ (B.Λ (j + 1)) → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V j).rank) χj vac (d : WO (c.V j) (c.V (j + 1)) →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V j) (c.V (j + 1)) sS sT (B.Λ j : Set _) (B.Λ (j + 1) : Set _) (B.β j) (B.β (j + 1)) LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ j) (B.Λ (j + 1)) S g → om (B.b j, B.b (j + 1)) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).eL j)) (om (B.b j, B.b (j + 1)) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  have hn : ∀ i, ∃ n, j + n = (G i).s := fun i => ⟨(G i).s - j, by have := (G i).hs; omega⟩
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).eL j) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain ⟨n, hn⟩ := hn i
    exact ((E i).eL_at j n hn).1
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, -, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, -, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd j (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ j (n + 1) (by omega))) mS
        ((G i).latY j (n + 1) _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' (hv.sd (j + 1) hj) hmv' _ (eb.symm.trans (stdOrd _ _ (j + 1) n (by omega))) mT
        ((G i).latY (j + 1) n _) π' hπ⟩
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, ha, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, hb, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ _ _ _ mS mT ((E i).reg.1 j n hn) rfl ((E i).eL_at j n hn)

theorem step_top : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j (h : j + 2 * 0 + 2 = D.R.m), GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → GlobalTheory.FinPl.Moves c.T B.bT B.ΛT v.NT S → B.b (j + 1) ∈ GfC (c.V (j + 1)) → B.bT ∈ GfC c.T → IsSelfDualC _ (B.Λ (j + 1)) → IsSelfDualC _ B.ΛT → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V (j + 1)).rank) χj vac (d : WO (c.V (j + 1)) c.T →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V (j + 1)) c.T sS sT (B.Λ (j + 1) : Set _) (B.ΛT : Set _) (B.β (j + 1)) B.βT LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V (j + 1)) c.T χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ (j + 1)) B.ΛT S g → om (B.b (j + 1), B.bT) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).toAt.eT j h)) (om (B.b (j + 1), B.bT) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).toAt.eT j hj) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    exact (E i).eLT_at.1
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, -, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, -, mT⟩ := (G i).frameTop
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd _ (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ _ 0 rfl)) mS
        ((G i).latY _ 0 _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' hv.sdT hmv' _ eb.symm mT (G i).latT π' hπ⟩
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, ha, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, hb, mT⟩ := (G i).frameTop
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ (Equiv.refl _) _ _ mS mT (E i).reg.2.1 rfl (E i).eLT_at

end GlobalTheory.QVecJoin
end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QVecJoin

theorem natCast_mem_under {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) :
    ((n : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal ↔ ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((n : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem false_of_coprime_mem {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hb : ((b : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have ha' : ((a : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 ha
  have hb' : ((b : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hb
  exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hab (ringChar.dvd ha') (ringChar.dvd hb'))

theorem isWeilDatum_cast {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

theorem qVec_pinTup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t,
    QVec (a.fam row col) ((famOf a J row col hCh t).pinTup sc cT) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat J hJ row col hCh sc cT t
  have hC3 := hW.pk.bot.hyp.2.2.2.1
  have hL := hC3.lev
  obtain ⟨hinj, hund⟩ := GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t (J t) (hJ t)
  have hV := (ha.tie row col).1

  have hQS : ∀ p, p ∈ ((famOf a J row col hCh t).pinTup sc cT).Q ↔ ∃ i, ((J t).G i).q.v = p := by
    intro p
    simp only [QFam.pinTup, famOf, Finset.mem_image]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
  have hSQ : ∀ p, (∃ i, ((J t).G i).q.v = p) ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, hund i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, rfl⟩ := (hJ t).surj PP hPP
      exact ⟨i, hund i⟩
  have hQiff : ∀ PP, PP ∈ (pk W).Q t ↔ ∃ i, (J t).pl i = PP := fun PP =>
    ⟨fun h => (hJ t).surj PP h, by rintro ⟨i, rfl⟩; exact (J t).mem i⟩
  have hrk : ∀ i, (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (((J t).G i).s + 1) := by
    intro i
    have e1 : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m - 1 := rfl
    have e2 := ((J t).G i).hs
    omega

  have gIn : ∀ PP ∈ (pk W).Pg, ∃ k, (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    refine ⟨k, ?_⟩
    have hmemK : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ (PP.under (𝓞 (I.rec7 l Z).host.K)).asIdeal := by
      have hk' : PP.under (𝓞 (I.rec7 l Z).host.K) = (pk W).C.P.pb k := hk
      rw [hk']
      exact (pk W).C.P.pb_over k
    have h2 : algebraMap (𝓞 (I.rec7 l Z).host.K) (𝓞 (I.rec7 l Z).host.E) (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hoff : ∀ p, (∃ i, ((J t).G i).q.v = p) → p ∉ a.v.gP := by
    intro p hp hxg
    obtain ⟨PP, hPP, rfl⟩ := (hSQ p).1 hp
    obtain ⟨PP', hPP', e⟩ := (hV.gP _).1 hxg
    obtain ⟨k, hk⟩ := gIn PP' hPP'
    have hg : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal :=
      (natCast_mem_under PP _).1 (e ▸ (natCast_mem_under PP' _).2 hk)
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hPP
    haveI : PP.asIdeal.IsPrime := PP.isPrime
    haveI : Finite (Formalism.L2.DIV.kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    haveI : Fintype (Formalism.L2.DIV.kP PP) := Fintype.ofFinite _
    have hq0 : ((q : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
      have h0q : ((q : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
        rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP PP)
      exact (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).1 (by simpa using h0q)
    exact false_of_coprime_mem PP ((Nat.coprime_primes hq ((I.rec7 l Z).host.g_prime k)).2 (hne k)) hq0 hg
  have hS : (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) = (fun p => ∃ i, ((J t).G i).q.v = p) :=
    funext fun p => propext (hQS p)
  have hmv : ∀ j, j < (I.rec7 l Z).R.m → GlobalTheory.FinPl.Moves _ (a.g.b j) ((pk W).ΛY j) (a.v.N j) (fun p => ∃ i, ((J t).G i).q.v = p) :=
    fun j hj => hV.moves j hj _ hoff
  have hb : ∀ j, a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := fun j => (hV.b j) ▸ ha.vis.b j
  have hS' : (fun p => ∃ i, ((J t).G i).q.v = p) = fun p => ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) :=
    funext fun p => propext (hSQ p)
  have sdY : ∀ j, j < (I.rec7 l Z).R.m → IsSelfDualC (Yc (I.rec7 l Z) j) ((pk W).ΛY j) := fun j hj =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY j hj)
  have sdX : IsSelfDualC (I.rec7 l Z).sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX
  refine ⟨?_, ?_⟩
  · intro j hj d hd g hg
    have hmid : ((famOf a J row col hCh t).pinTup sc cT).eQ j = aconv (List.ofFn fun i => ((J t).E i).eL j) := if_pos hj
    rw [hmid]
    rw [hS] at hg
    exact step_mid (I.rec7 l Z) (commOf (pk W) u a.g) a.v (baseOf (pk W) (lvP W) u a.g) (chrK W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((pk W).xiR t) ((pk W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv j (by omega)) (hmv (j + 1) hj) (hb j) (hb (j + 1)) (sdY j (by omega)) (sdY (j + 1) hj) _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _ (hC3.chain.ωY t j hj) g hg
  · intro j hj d hd g hg
    rw [hS] at hg
    have hmT : GlobalTheory.FinPl.Moves _ a.g.bT (pk W).ΛX a.v.NT (fun p => ∃ i, ((J t).G i).q.v = p) := by
      rw [hV.bT.2]; exact hV.movesT _
    have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
      have h1 := ha.vis.bT
      rwa [hV.bT.1] at h1
    exact step_top (I.rec7 l Z) (commOf (pk W) u a.g) a.v (baseOf (pk W) (lvP W) u a.g) (chrK W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((pk W).xiR t) ((pk W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv (j + 1) (by omega)) hmT (hb (j + 1)) hbT (sdY (j + 1) (by omega)) sdX _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _
      (isWeilDatum_cast ((pk W).ωX t) (hC3.chain.ωX t) (j + 1) (idx_top hj)) g hg

end GlobalTheory.QVecJoin

end
