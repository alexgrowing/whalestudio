import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.KernelLattices.KerMtPin
import Formalism.LocalToGlobal.KernelLattices.KerMemPin

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def TopPt (u : B.Word) (a : I.ι) (k : GA B (B.R.N B.R.m)) : Prop :=
  ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
    IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
    PtOf (g * k) (tilF I.sel (I.tup a) u d)

def ReadsTop (u : B.Word) (a : I.ι) {Ch : Type} (chOf : (I.stp u a B.R.m).Cl → Ch)
    (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N B.R.m))) (chi : ∀ β, U β →* ℂˣ)
    (y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)) (st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E) : Prop :=
  ∃ k, I.Reads u a B.R.m chOf Lb U chi y st k ∧ ∀ β, I.TopPt l Z u a (k β)

set_option maxHeartbeats 800000 in

theorem ReadsTop.mem_chi {u : B.Word} {a : I.ι} {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)} {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E}
    (h : I.ReadsTop l Z u a chOf Lb U chi y st) (c : (I.stp u a B.R.m).Cl) (d : XPt (B.primes X) B.R I.sel (I.tup a))
    (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)) (hc : ((I.stp u a B.R.m).rep c).1.1 = tilF I.sel (I.tup a) u d) (hd : PtOf g' d)
    (hg : IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1) :
    ∃ hm : g⁻¹ * y c ∈ U (chOf c), chi (chOf c) ⟨_, hm⟩ = 1 := by
  obtain ⟨k, hR, hk⟩ := h
  have h1 : (I.stp u a B.R.m).act c.1 1 ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c :=
    @one_smul _ _ _ ((I.stp u a B.R.m).actD c.1) _
  have e : y c * ((y c)⁻¹ * g) * k (chOf c) = g * k (chOf c) := by group
  have hq : PtOf (y c * ((y c)⁻¹ * g) * k (chOf c)) ((I.stp u a B.R.m).act c.1 1 ((I.stp u a B.R.m).rep c)).1.1 := by
    rw [e, h1, hc]
    exact hk _ d g' g hd hg
  have hx : (y c)⁻¹ * g ∈ U (chOf c) := (hR.lev c _ _ hq).2 ⟨1, map_one _, rfl, by rw [h1]⟩
  have hχ := hR.chr c ⟨_, hx⟩ 1 (map_one _) hq
  rw [map_one, Units.val_one, map_one] at hχ
  have e2 : g⁻¹ * y c = ((y c)⁻¹ * g)⁻¹ := by group
  refine ⟨e2 ▸ inv_mem hx, ?_⟩
  have e3 : (⟨g⁻¹ * y c, e2 ▸ inv_mem hx⟩ : U (chOf c)) = (⟨_, hx⟩ : U (chOf c))⁻¹ := Subtype.ext e2
  rw [e3, map_inv, inv_eq_one]
  exact Units.ext hχ

theorem ReadsTop.topBase {u : B.Word} {a : I.ι} {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)} {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E}
    (h : I.ReadsTop l Z u a chOf Lb U chi y st) (β : Ch) (hβ : ∀ c, U (chOf c) = U β) : I.TopBase l Z u a (U β) y :=
  fun c d g' g hc hd hg => hβ c ▸ (h.mem_chi I l Z c d g' g hc hd hg).1

def ReadsKTop (u : B.Word) (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a B.R.m).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad B.R.m le_rfl (fun c : {c // chOf c = β} => (I.chain l u a).stab B.R.m c.1)
      (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))) : Prop :=
  I.ReadsTop l Z u a chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1)

theorem ReadsKTop.readsK {u : B.Word} {a : I.ι} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad B.R.m le_rfl (fun c : {c // chOf c = β} => (I.chain l u a).stab B.R.m c.1)
      (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))} (h : I.ReadsKTop l Z u a chOf K) :
    I.ReadsK l Z u a B.R.m le_rfl chOf K :=
  h.imp fun _ hk => hk.1

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

structure StdP {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) (E : TwPEvzS P) : Prop where

  what₂ : ∀ u a ha, I.ReadsP a (P.cls u a ha).lev.Lb (P.cls u a ha).lev.U (P.cls u a ha).lev.chi (fun c => ((P.cls u a ha).y c).1)
    (P.cls u a ha).lat fun c s => ((P.cls u a ha).stabI c s).1

  eW : ∀ u a ha z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → (P.val u a ha).eW z c s = z c s'

  z0 : ∀ u a ha h1, (P.til u a ha h1).z0 = TC.z0 X u

  eWz : ∀ u a z, E.eWz u a z = z

def TopK (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) : Prop := ∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m),
  I.ReadsTop l Z u a (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
    (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
    (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
    (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1)

variable {I l Z l0} {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W}

theorem StdP.lat_eq {P : TwPTiedS Lv} {E : TwPEvzS P} (h : I.StdP l Z l0 P E) (u a ha) (c : (I.stX a).Cl) :
    (P.cls u a ha).lat c = ((I.stX a).rep c).1.1.deco.1.N :=
  (h.what₂ u a ha).lat c

theorem StdP.unique {P P' : TwPTiedS Lv} {E : TwPEvzS P} {E' : TwPEvzS P'} (h : I.StdP l Z l0 P E) (h' : I.StdP l Z l0 P' E') (u a) :
    E.eWz u a = E'.eWz u a ∧ ∀ ha, (∀ c, (P.cls u a ha).lat c = (P'.cls u a ha).lat c) ∧
      ∀ h1, (P.til u a ha h1).z0 = (P'.til u a ha h1).z0 :=
  ⟨LinearEquiv.ext fun z => (h.eWz u a z).trans (h'.eWz u a z).symm,
    fun ha => ⟨fun c => (h.lat_eq u a ha c).trans (h'.lat_eq u a ha c).symm,
      fun h1 => (h.z0 u a ha h1).trans (h'.z0 u a ha h1).symm⟩⟩

end Tw

def StdTw (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)} {nch : NChoice (I.rec7 l Z)}
    {tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch} {C : ColsTiedSym (I.rec7 l Z)} (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) : Prop :=
  I.StdW l Z l0 t.forms ∧ I.StdLv l Z l0 t.lv ∧ I.StdP l Z l0 t.pt t.ptE

def EntOk {D : D7} {Y : DivX D} {Tw : TwForms D} (E : KerEnt D Y Tw) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  (∃ kf : ∀ u μ w, LevFree Y u μ w → GL3Columns.KFTie E (O u μ) w, ∀ u μ w (h : LevFree Y u μ w), (kf u μ w h).UnIs) ∧ AdaptedTh E O

example (u : B.Word) (j : Fin (B.R.N B.R.m)) (hj : j.1 + 1 = B.R.N B.R.m) :
    TC.z0 X u j = ((X.piT u : 𝓞 B.host.E) : B.host.E) := if_pos hj

example (u : B.Word) (j : Fin (B.R.N B.R.m)) (hj : j.1 + 1 ≠ B.R.N B.R.m) : TC.z0 X u j = 0 := if_neg hj

end GlobalTheory.Mem.Col2.TC

end
