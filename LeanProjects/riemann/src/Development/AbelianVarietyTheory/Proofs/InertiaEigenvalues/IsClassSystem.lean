import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSetup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move

structure SameGeo (D D' : D7) : Prop where
  R : D.R = D'.R
  host : HEq D.host D'.host
  sp : HEq D.sp D'.sp
  Tau : D.what₂.Tau = D'.what₂.Tau
  instTau : HEq D.what₂.instTau D'.what₂.instTau
  eTau : HEq D.eTau D'.eTau
  hc : HEq D.hc D'.hc

theorem CopyTw.sameGeo {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) :
    SameGeo D D' := ⟨h.gal.R, h.gal.host, h.sp, h.Tau, h.instTau, h.eTau, h.hc⟩

scoped macro "geo_cases " h:ident D:ident D':ident : tactic =>
  `(tactic| (
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := $h
    cases $D:ident with | mk R host sp vol volp what₂ eTau hc => ?_
    cases $D':ident with | mk R' host' sp' vol' volp' rows' eTau' hc' => ?_
    dsimp only at a1 a2 a3 a4 a5 a6 a7
    subst a1; subst a2; subst a3
    cases what₂; cases rows'
    dsimp only at a4 a5 a6 a7
    subst a4; subst a5; subst a6; subst a7))

variable {D D' : D7}

structure RecipRel {Ω Ω' : Type} [Field Ω] [Algebra D.host.E Ω] [Field Ω'] [Algebra D'.host.E Ω'] (a : Recip D Ω) (a' : Recip D' Ω') :
    Prop where
  κ : HEq a.κ a'.κ
  art : HEq a.art a'.art

structure TwistRel {A : Type} [CommGroup A] (t : Twist D A) (t' : Twist D' A) : Prop where
  Q : HEq t.Q t'.Q
  chi : HEq t.chi t'.chi
  res : HEq t.res t'.res

structure FrameRel {S T : HSp D} {S' T' : HSp D'} (F : Frame S T) (F' : Frame S' T') : Prop where
  ψ : HEq F.ψ F'.ψ
  θ : HEq F.θ F'.θ
  sT : HEq F.sT F'.sT
  BS : HEq F.BS F'.BS
  BT : HEq F.BT F'.BT
  ΛS : HEq F.ΛS F'.ΛS
  ΛT : HEq F.ΛT F'.ΛT
  βS : HEq F.βS F'.βS
  βT : HEq F.βT F'.βT
  f₀ : HEq F.f₀ F'.f₀

structure TypeRel {r r' : ℕ} (G : TypeDat D r) (G' : TypeDat D' r') : Prop where
  Pg : HEq G.Pg G'.Pg
  P : HEq G.P G'.P
  mu : HEq G.mu G'.mu

structure WeightRel {n n' : ℕ} (w : Weight D n) (w' : Weight D' n') : Prop where
  p : HEq w.p w'.p
  q : HEq w.q w'.q
  ap : HEq w.ap w'.ap
  am : HEq w.am w'.am
  c : HEq w.c w'.c
  lam : HEq w.lam w'.lam

structure BaseRel {S T : HSp D} {S' T' : HSp D'} (B : Base S T) (B' : Base S' T') : Prop where
  F : FrameRel B.F B'.F
  G : TypeRel B.G B'.G
  de : TwistRel B.de B'.de
  w : WeightRel B.w B'.w
  mu0 : HEq B.mu0 B'.mu0
  eta : HEq B.eta B'.eta

theorem TwistRel.good (h : SameGeo D D') {A : Type} [CommGroup A] {t : Twist D A} {t' : Twist D' A} (r : TwistRel t t')
    (g : t.Good) : t'.Good := by
  geo_cases h D D'
  obtain ⟨Q, chi, res⟩ := t
  obtain ⟨Q', chi', res'⟩ := t'
  obtain ⟨r1, r2, r3⟩ := r
  cases r1; cases r2; cases r3
  exact ⟨g.1, g.2, g.3, g.4, g.5, g.6⟩

scoped macro "base_cases " r:ident B:ident B':ident : tactic =>
  `(tactic| (
    obtain ⟨hr, ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, _, _⟩ := $B
    obtain ⟨hr', ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, _, _⟩ := $B'
    obtain ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩, ⟨g1, g2, g3⟩, ⟨d1, d2, d3⟩, ⟨w1, w2, w3, w4, w5, w6⟩, m1, m2⟩ := $r
    dsimp only at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 g1 g2 g3 d1 d2 d3 w1 w2 w3 w4 w5 w6 m1 m2
    subst f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 g1 g2 g3 d1 d2 d3 w1 w2 w3 w4 w5 w6 m1 m2))

theorem BaseRel.good (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') (g : B.Good) : B'.Good := by
  have gd := r.de.good h g.de
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  have v := g.frame.vac.2
  refine ⟨g.even, g.odd, ⟨g.frame.1, g.frame.2, g.frame.3, g.frame.4, g.frame.5, g.frame.6, g.frame.7, g.frame.8, g.frame.vac.1, ?_⟩,
    gd, ⟨g.places.1, g.places.2, g.places.3⟩, ⟨g.wt.1, g.wt.2⟩, g.sig, g.sigOK, g.eta, g.hecke, g.real, g.unram, g.tame, g.inf⟩
  exact ⟨v.1, ⟨v.2.1, v.2.2, v.2.3, v.2.4⟩, v.3, v.4, v.5⟩

theorem BaseRel.isWeil (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') {ν : (AE D)ˣ →* Circle} {ν' : (AE D')ˣ →* Circle} (hν : HEq ν ν')
    {ω : PairRep S T} {ω' : PairRep S' T'} (hω : HEq ω ω') (g : B.IsWeil ν ω) : B'.IsWeil ν' ω' := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  subst hν; subst hω
  refine ⟨g.1, g.2, g.3, g.4, g.5, fun p f a => ?_, fun x y w f a => g.7 x y w f ⟨a.1, a.2, a.3, a.4⟩,
    fun x hx y hy f a => g.8 x hx y hy f ⟨a.1, a.2, a.3, a.4⟩, fun f a => g.9 f ⟨a.1, a.2, a.3, a.4⟩,
    fun μ F h1 h2 p f a => g.10 μ F h1 h2 p f ⟨a.1, a.2, a.3, a.4⟩, fun e he x y h1 h2 z w h3 h4 => ?_⟩
  · have b := g.6 p f ⟨a.1, a.2, a.3, a.4⟩
    exact ⟨b.1, b.2, b.3, b.4⟩
  · obtain ⟨r, hr, h5⟩ := g.11 e he x y h1 h2 z w h3 h4
    exact ⟨r, hr, fun l h6 f a => h5 l (fun u hu f a => h6 u hu f ⟨a.1, a.2, a.3, a.4⟩) f ⟨a.1, a.2, a.3, a.4⟩⟩

theorem BaseRel.adm (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') {Q : Finset (Pl D.host.E)} {Q' : Finset (Pl D'.host.E)} (hQ : HEq Q Q')
    (g : B'.admitted Q') : B.admitted Q := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  subst hQ
  exact ⟨⟨g.1.1, g.1.2, g.1.3⟩, g.2⟩

theorem BaseRel.isClassSystem (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') {t : Twist D Circle} {t' : Twist D' Circle} (ht : TwistRel t t') {I I' : Type} (hI : I = I')
    {y : I → GA D S} {y' : I' → GA D' S'} (hy : HEq y y') (g : IsClassSystem S (B.levJ t) y) :
    IsClassSystem S' (B'.levJ t') y' := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  obtain ⟨Q, chi, res⟩ := t
  obtain ⟨Q', chi', res'⟩ := t'
  obtain ⟨r1, r2, r3⟩ := ht
  cases r1; cases r2; cases r3
  subst hI; subst hy
  exact ⟨g.1, g.2, g.3⟩

theorem BaseRel.isBaseFrame (h : SameGeo D D') {S T : HSp D} {S' T' : HSp D'} (hS : HEq S S') (hT : HEq T T') {B : Base S T}
    {B' : Base S' T'} (r : BaseRel B B') :
    (Lev.IsBaseFrame S B.F.βS B.F.ΛS 1 → Lev.IsBaseFrame S' B'.F.βS B'.F.ΛS 1) ∧
    (Lev.IsBaseFrame T B.F.βT B.F.ΛT 1 → Lev.IsBaseFrame T' B'.F.βT B'.F.ΛT 1) ∧
    ((∀ P ∈ B.G.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k)) → ∀ P ∈ B'.G.Pg, ∃ k, P ∈ placesOver D'.host.E (D'.host.g k)) := by
  geo_cases h D D'
  subst hS; subst hT
  base_cases r B B'
  exact ⟨id, id, id⟩

theorem SameGeo.symm (h : SameGeo D D') : SameGeo D' D :=
  ⟨h.R.symm, h.host.symm, h.sp.symm, h.Tau.symm, h.instTau.symm, h.eTau.symm, h.hc.symm⟩

theorem SameGeo.spaces (h : SameGeo D D') {j : Fin D.R.m} {j' : Fin D'.R.m} (hj : (j : ℕ) = j') :
    HEq (Vc D j) (Vc D' j') ∧ HEq (Wc D j) (Wc D' j') ∧ (Vc D j).rank = (Vc D' j').rank ∧ (Wc D j).rank = (Wc D' j').rank ∧
    HEq (fun τ => aPl D j ((Wc D j).sig (tauE D τ)).1 τ) (fun τ => aPl D' j' ((Wc D' j').sig (tauE D' τ)).1 τ) ∧
    HEq (fun τ => aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ)
      (fun τ => aMi D' j' ((Wc D' j').sig (tauE D' τ)).1 ((Wc D' j').sig (tauE D' τ)).2 τ) := by
  geo_cases h D D'
  cases Fin.ext hj
  exact ⟨HEq.rfl, HEq.rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem SameModel.cart_onb (h : SameGeo D D') {V : HSp D} {V' : HSp D'} (hV : HEq V V') {P : D.what₂.Tau → SPar}
    {P' : D'.what₂.Tau → SPar} {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (r : SameModel M M') :
    HEq (cart M) (cart M') ∧ HEq (onb M) (onb M') := by
  have h1 := r.ε
  have h2 := r.fr
  clear r
  geo_cases h D D'
  subst hV
  cases M; cases M'
  dsimp only at h1 h2
  subst h1; subst h2
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem SameGeo.chrEq (h : SameGeo D D') {c : (AE D)ˣ →* Circle} {c' : (AE D')ˣ →* Circle} (hc : HEq c c')
    {χ : Formalism.L2.Host.HChar D.host.E} {χ' : Formalism.L2.Host.HChar D'.host.E} (hχ : HEq χ χ') (g : ChrEq c χ) : ChrEq c' χ' := by
  geo_cases h D D'
  subst hc; subst hχ
  exact g

section Setup

variable {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}

structure SetupRel (ρ : Setup X) (ρ' : Setup X') : Prop where
  rc : RecipRel ρ.rc ρ'.rc
  ch : HEq ρ.ch ρ'.ch
  bad : HEq ρ.bad ρ'.bad
  e : HEq ρ.e ρ'.e
  ek : HEq ρ.ek ρ'.ek
  B : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b, BaseRel (ρ.B i j b) (ρ'.B i' j' b)
  om : HEq ρ.om ρ'.om
  Cl : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b t t', TwistRel t t' →
    ρ.Cl i j b t = ρ'.Cl i' j' b t'
  rep : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b t t', TwistRel t t' →
    HEq (ρ.rep i j b t) (ρ'.rep i' j' b t')
  β : HEq ρ.β ρ'.β
  eG : ∀ i i', HEq i i' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ b, HEq (ρ.eG i j b) (ρ'.eG i' j' b)

end Setup

theorem TwistRel.eq {A : Type} [CommGroup A] {t t' : Twist D A} (r : TwistRel t t') : t = t' := by
  obtain ⟨Q, chi, res⟩ := t
  obtain ⟨Q', chi', res'⟩ := t'
  obtain ⟨r1, r2, r3⟩ := r
  cases r1; cases r2; cases r3
  rfl

theorem BaseRel.refl {S T : HSp D} (B : Base S T) : BaseRel B B :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, .rfl, .rfl⟩

theorem BaseRel.eq {S T : HSp D} {B B' : Base S T} (r : BaseRel B B') : B = B' := by
  base_cases r B B'
  rfl

theorem SetupRel.refl {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X) : SetupRel ρ ρ where
  rc := ⟨.rfl, .rfl⟩
  ch := .rfl
  bad := .rfl
  e := .rfl
  ek := .rfl
  B i i' hi j j' hj b := by cases hi; cases Fin.ext hj; exact .refl _
  om := .rfl
  Cl i i' hi j j' hj b t t' ht := by cases hi; cases Fin.ext hj; cases ht.eq; rfl
  rep i i' hi j j' hj b t t' ht := by cases hi; cases Fin.ext hj; cases ht.eq; rfl
  β := .rfl
  eG i i' hi j j' hj b := by cases hi; cases Fin.ext hj; rfl

theorem SetupRel.eq {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ ρ' : Setup X} (r : SetupRel ρ ρ') :
    ρ = ρ' := by
  obtain ⟨⟨κ, art⟩, ch, bad, e, ek, B, om, Cl, rep, β, eG⟩ := ρ
  obtain ⟨⟨κ', art'⟩, ch', bad', e', ek', B', om', Cl', rep', β', eG'⟩ := ρ'
  obtain ⟨⟨r1, r2⟩, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := r
  dsimp only at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  subst r1 r2 r3 r4 r5 r6 r8 r11
  obtain rfl : B = B' := funext fun i => funext fun j => funext fun b => (r7 i i .rfl j j rfl b).eq
  obtain rfl : Cl = Cl' := funext fun i => funext fun j => funext fun b => funext fun t => r9 i i .rfl j j rfl b t t ⟨.rfl, .rfl, .rfl⟩
  obtain rfl : rep = rep' := funext fun i => funext fun j => funext fun b => funext fun t =>
    eq_of_heq (r10 i i .rfl j j rfl b t t ⟨.rfl, .rfl, .rfl⟩)
  obtain rfl : eG = eG' := funext fun i => funext fun j => funext fun b => eq_of_heq (r12 i i .rfl j j rfl b)
  congr 1
  exact Subsingleton.elim _ _

end GlobalTheory.TwInputs.Move

end
