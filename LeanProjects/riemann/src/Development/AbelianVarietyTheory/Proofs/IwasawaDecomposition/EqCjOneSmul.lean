import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef

namespace GlobalTheory.Mem.R3.Rw.WeilExt

section Defs

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

def LevSame (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.toLevCh.mu (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((i' : ℕ) + 1)) (z.R.toLevCh.mu (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((i : ℕ) + 1)) ∧
    ∀ PP' PP, HEq PP' PP → PP ∈ z.R.Pg → HEq (R'.chi ((i' : ℕ) + 1) PP') (z.R.chi ((i : ℕ) + 1) PP)) ∧
  HEq R'.eta z.R.eta ∧ R'.Q (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) = ∅ ∧ z.R.Q (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) = ∅

def IdemSame (z : Dat (w.st Z) w.I hX T Wt) (Xg : Finset (Gc B' w'.px → B'.LL)) : Prop :=
  ∀ (g' : Gc B' w'.px) (g : Gc B w.px), HEq g' g → B'.embLL ((idemOf Xg).coeff g') = B.embLL ((idemOf z.Xg).coeff g)

set_option maxHeartbeats 1000000 in

def JSpan (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ x' : (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.fam.amb.FL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))),
      ∃ (n : ℕ) (a : Fin n → (w'.st Z').toD7.what₂.LL)
        (x : Fin n → (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))),
        HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x') (∑ k, (w'.st Z').toD7.what₂.embLL (a k) • z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (x k))

end Defs

theorem ratAt_of_geo {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F)
    (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (hI : GlobalTheory.RealGeo.InGeo geo) (hU : R.toRealDat.LUnif) :
    RatAt R.toRealDat A3.A.μ0 := by
  intro i x v hv
  have hio := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A3.A _ R.toRealDat hch.base.lev hch.base.fam hch.base.models
    (RealDat.thP_of_weak hch.base.thP hEx)
  have hM := GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ C R F geo.κ geo.v₀ geo.O (fun _ => 1) hn hch hEx ⟨geo.fw⟩ hio i
    (geo.pins i) (geo.phase i hU)
  have e : v = R.jV i A3.A.μ0 x := (hch.base.models.HV i _).1 (hv.trans (hch.base.models.jV i _ x).symm)
  subst e
  obt ⟨y, hy⟩ := (Formalism.IndefR.FWT.phase_of_oneMap geo.fw hU
    (hI.evInj i _ (Formalism.IndefR.FWT.base_embedding_good C R.toRealDat geo.fw.alg_eq geo.fw.laws.pins.2.2.1)) (geo.O i) (geo.phase i hU hM.1)).2 x
  exact ⟨y, hy.trans (one_smul ℂ _)⟩

theorem eq_cj_one_smul {H : Type} [AddCommGroup H] [Module ℂ H] (s : Bool) (v : H) : v = Formalism.IndefR.Links.cj s (1 : ℂ) • v := by
  rw [map_one, one_smul]

local macro "qmove " h:term : tactic => `(tactic| (
  obtain ⟨i, u, a, l, e, m, w, b, x, k⟩ := $h
  refine ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, a, l, e, m, w, b, x, fun c hc => ?_⟩
  have kv := k c hc
  exact ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩))

set_option maxHeartbeats 8000000 in

theorem charW_keep (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (hI : Inputs X.toD7)
    (hXi : IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A)
    (hEx : ∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.ExAt)
    (S : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks → Prop)
    (hSM : ∀ R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG, S R →
      S (updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG))
    (hS3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, S R → S (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (hS6 : ∀ R kap lam, S R → S (R.upd6 kap lam)) (s0 : S R₀.toRealDat)
    (p0 : R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2) (i0 : R₀.IsInert) (t0 : R₀.IsTup) (a0 : R₀.AllPlaces)
    (k0 : Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG) (b0 : BrgStd X I hX U Xg tr₀ R₀.toRealDat) (x0 : R₀.toRealDat.grp_chiW)
    (hW : ModW R₀.toRealDat) (hω : WeilAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hV : ModVAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0)
    (hl : LiftAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hr : RatAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) :
    ∃ (tr : TrI X.B px) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧
      R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ BrgStd X I hX U Xg tr R.toRealDat ∧ S R.toRealDat ∧
      SameAt (A := (famR X I hX U Xg tr₀).A) R₀.toRealDat R.toRealDat (famR X I hX U Xg tr₀).A.μ0 := by
  classical
  obt ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A Ks (face0 X I hX U Xg tr₀).lv2
  obt ⟨R1, p1, c1, t1, f1, g1, ⟨q1, s1⟩, m1, hrat⟩ := exists_weak_keep hI hXi hL hF
    (fun R => (RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      BrgStd X I hX U Xg tr₀ R ∧ R.grp_chiW ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c) ∧ S R)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 ⟨h, s⟩ => ⟨by qmove h, hSM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 ⟨h, s⟩ => ⟨by qmove h, hS3 _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    R₀.toRealDat p0 ⟨⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, b0, x0, fun c hc => by cases eq_of_heq hc; exact k0⟩, s0⟩ hW hω hV hl hr
  obtain ⟨i1, u1, a1, l1, e1, mu1, w1, b1, x1, k1⟩ := q1
  have hc : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  obtain ⟨cutoffDeriv, hcG1⟩ := hc
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  have htr : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  obtain ⟨tr, htr⟩ := htr
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obt ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have p6 := RealDat.preliminary_of_scalar_update p1 kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update f1 kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update c1 kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update t1 kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update g1 kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obt ⟨y, hy⟩ := hrat i x
    refine ⟨y, ?_⟩
    exact (by with_unfolding_all exact (hy.trans (eq_cj_one_smul (twAt X.toD7.what₂.embLL (famR X I hX U Xg tr₀).A.v0) _) :))
  have kv := k1 cutoffDeriv hcG1
  exact ⟨tr, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, x1⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6, l1, e1, hcG1, mu1, w1, b1, hS6 _ kap R2.lam s1, m1⟩

end GlobalTheory.Mem.R3.Rw.WeilExt

end
