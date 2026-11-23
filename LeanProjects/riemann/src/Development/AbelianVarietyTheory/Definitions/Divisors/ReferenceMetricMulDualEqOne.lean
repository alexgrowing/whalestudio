import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

theorem posAt_of_posSet {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv} {m : Var.Met Y σ Δ}
    (h : m.posSet = Set.univ) (z : Pts Y σ) : PosAt (C := cxSt F) m z :=
  have h₁ : z ∈ Var.eqnSet σ Δ (eqn Δ (under z)) := Base.isEqn_eqn _ _
  ((Var.Met.mem_posSet_iff h₁).1 (h ▸ Set.mem_univ z)).trans_eq (Var.pn_frame h₁).symm

section Met

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

abbrev PolOf (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

def metTrue (x : ToroidalCompactificationData s) (Φ : s.Flag) (P : PolOf x Φ) : MetIn Φ where
  hm := metsOf x Φ
  h0 := refMet x Φ
  r := rFlag x Φ
  ab := P.ab
  dir := P.dir
  reg := P.reg

theorem pn_met_mul_neg {Φ : s.Flag} {k : s.Comp} {σ : D.what₂.LL →+* ℂ} (G : EigMet s.T.Z (embOf κ.e σ))
    (n : Letter S.Dw → ℤ) {z : Pts (Φ.C k).Y σ} {f : (Φ.C k).Y.Fn} (hf : (divOf (Φ.C k) n).GeneratesAt (under z) f) :
    (cxSt _).pn _ σ _ ((Φ.C k).met G n) ((cxSt _).cx _ σ f) z *
      (cxSt _).pn _ σ _ ((Φ.C k).met G (-n)) ((cxSt _).cx _ σ f⁻¹) z = 1 := by
  have h0 : f ≠ 0 := have ⟨_, _, hu⟩ := hf; left_ne_zero_of_mul hu.ne_zero
  let a : (Φ.C k).Y.Fnˣ := Units.mk0 f h0
  have h₁ : (divOf (Φ.C k) n).IsEqn (under z) a⁻¹ := CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa [a] using hf)
  have h₂ : (divOf (Φ.C k) (-n)).IsEqn (under z) a := by
    have e : divOf (Φ.C k) (-n) = (-1 : ℤ) • divOf (Φ.C k) n := by simp [divOf]
    simpa [e] using h₁.zsmul (-1)
  have e₁ := Var.pn_frame (m := (Φ.C k).met G n) (y := z) h₁
  have e₂ := Var.pn_frame (m := (Φ.C k).met G (-n)) (y := z) h₂
  rw [inv_inv] at e₁
  rw [Units.val_inv_eq_inv_val] at e₂
  refine (congrArg₂ (· * ·) e₁ e₂).trans ((FlagCpt.met_add_h G n (-n) h₁ h₂).symm.trans ?_)
  have e₃ : Var.val z (1 : (Φ.C k).Y.FnC σ) = 1 := by simpa using (Var.val_cx (y := z) 1).trans (Base.ratVal_one _)
  simp [FlagCpt.met, FlagCpt.genSq, prodPow, Var.tv, e₃]

end Met

namespace Setup

variable {D : D7} (O : Setup D)

structure CoreWith (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) : Prop where
  met : O.met = metTrue x O.Φ P
  Mb : O.Mb = mbarOf P
  bd : IsBdOf x O.L O.B
  fl : O.fl = flBetti O.s O.Φ O.L

def Core : Prop := ∃ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P

def withCore (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (h : ∃ B, IsBdOf x O.L B) : Setup D :=
  { O with met := metTrue x O.Φ P, Mb := mbarOf P, B := bdOf x O.L h, fl := flBetti O.s O.Φ O.L }

theorem coreWith_withCore (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (h : ∃ B, IsBdOf x O.L B) :
    (O.withCore x P h).CoreWith x P := ⟨rfl, rfl, isBdOf_bdOf x O.L h, rfl⟩

theorem coreWith_ofKit {A : Amb D} {N j : ℕ} (h : 1 ≤ j ∧ j < N) {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {L : CmList A}
    {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (k : Kit s L (cxSt D.what₂.LL) jC ng)
    (adm : AdmSt D N j jC) {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} (hB : IsBdOf x L k.B) (hf : k.fl = flBetti s k.Φ L)
    (hM : k.Mb = mbarOf P) : (ofKit h k adm (metTrue x k.Φ P)).CoreWith x P := ⟨rfl, hM, hB, hf⟩

namespace CoreWith

variable {O} {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} (h : O.CoreWith x P)
include h

theorem hm_eq : O.met.hm = metsOf x O.Φ := congrArg MetIn.hm h.met

theorem h0_eq : O.met.h0 = refMet x O.Φ := congrArg MetIn.h0 h.met

theorem r_eq : O.met.r = rFlag x O.Φ := congrArg MetIn.r h.met

theorem ab_eq : O.met.ab = P.ab := congrArg MetIn.ab h.met

theorem dir_eq : O.met.dir = P.dir := congrArg MetIn.dir h.met

theorem reg_eq : O.met.reg = P.reg := congrArg MetIn.reg h.met

theorem two_mul_chg (c : O.s.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) :
    2 * O.chg c none u σ z = phW (metsOf x O.Φ) (refMet x O.Φ) c σ u z := by
  rw [← h.hm_eq, ← h.h0_eq]
  rfl

theorem mbIs : O.MbIs := by
  obtain ⟨A, N, j, hi, S, κ, s, L, Φ, hd, B, fl, Mb, jC, ng, loc, glob, adm, met⟩ := O
  obtain ⟨h₁, h₂, -, -⟩ := h
  dsimp only at x P h₁
  subst h₁
  exact mbIs_of_eq _ P rfl rfl rfl h₂

end CoreWith

namespace Core

variable {O} (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ)
include h

theorem mbIs : O.MbIs := have ⟨_, _, h⟩ := h; h.mbIs

theorem strictAnti_dir (τ : D.what₂.Tau) : StrictAnti (O.met.dir τ) := by
  obtain ⟨_, P, h⟩ := h
  rw [h.dir_eq]
  exact P.strictAnti_dir τ

theorem ample_ab : (O.var c).ample (O.met.ab c).D := by
  obtain ⟨_, P, h⟩ := h
  rw [h.ab_eq]
  exact P.ab_ample c

theorem exp_le_r (z : Pts (O.var c) σ) : Real.exp 1 ≤ O.met.r c σ z := by
  obtain ⟨_, P, h⟩ := h
  rw [h.r_eq]
  exact exp_le_rFlag

theorem referenceMetric_mul_dual_eq_one (n : Letter O.S.Dw → ℤ) {z : Pts (O.var c) σ} {f : (O.var c).Fn}
    (hf : (divOf (O.Φ.C c) n).GeneratesAt (under z) f) :
    (cxSt _).pn _ σ _ (O.met.h0 c σ n) ((cxSt _).cx _ σ f) z *
      (cxSt _).pn _ σ _ (O.met.h0 c σ (-n)) ((cxSt _).cx _ σ f⁻¹) z = 1 := by
  obtain ⟨_, P, h⟩ := h
  rw [h.h0_eq]
  exact pn_met_mul_neg _ n hf

theorem referenceMetric_posAt (n : Letter O.S.Dw → ℤ) (z : Pts (O.var c) σ) : PosAt (O.met.h0 c σ n) z := by
  obtain ⟨x, P, h⟩ := h
  rw [h.h0_eq]
  exact posAt_of_posSet (posSet_refMet x O.Φ c σ n) z

theorem posAt_hm (R : Option ℝ) (n : Letter O.S.Dw → ℤ) (z : Pts (O.var c) σ) : PosAt (O.met.hm c R σ n) z := by
  obtain ⟨x, P, h⟩ := h
  rw [h.hm_eq]
  exact posAt_of_posSet (posSet_metsOf x O.Φ c R σ n) z

theorem chg_some_eq_zero {R : ℝ} (hR : 2 ≤ R) (u : D.what₂.Tau → Fin O.N → ℝ) {z : Pts (O.var c) σ}
    (hz : (O.Φ.C c).π (under z) ∈ genBd O.s.T.Z ∨ R ^ 3 ≤ O.met.r c σ z) : O.chg c (some R) u σ z = 0 := by
  obtain ⟨x, P, h⟩ := h
  rw [h.r_eq] at hz
  refine Finset.sum_eq_zero fun y _ => mul_eq_zero_of_right _ (sub_eq_zero.2 (congrArg (Real.log · / 2) ?_))
  rw [h.hm_eq, h.h0_eq]
  exact congrArg (_ * ·) (metsOf_some_eq hR hz _)

end Core

end Setup

def ObjCore {D : D7} (Y : DV.ShimX D.what₂.Tau) (A : SlopeTestRemainingChoices Y) (T : Real0 Y) (H : Ht Y) : Prop := ObjOf Setup.Core Y A T H

theorem ObjCore.withPs {D : D7} {Y : DV.ShimX D.what₂.Tau} {A : SlopeTestRemainingChoices Y} {T : Real0 Y} {H : Ht Y} (o : ObjCore Y A T H)
    (Ps : ℝ → Y.Comp → MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ) : ObjCore Y { A with Ps := Ps } T H :=
  ObjOf.withPs o Ps

example {D : D7} (O : Setup D) (τ : D.what₂.Tau) (h : O.met.dir = 0) : ¬ O.Core := fun hc => by
  have := O.indef
  have h1 := hc.strictAnti_dir τ (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (by simp)
  simp [h] at h1

example {D : D7} (O : Setup D) (hb : (genBd O.s.T.Z : Set (gen O.s.T.Z : Scheme.{0})).Nonempty) (c : O.s.Comp)
    (h : (O.B c).m = 0) : ¬ O.Core := fun ⟨_, _, hc⟩ => hc.bd.m_ne_zero c hb h

example {D : D7} (O : Setup D) (adm : AdmSt D O.N O.j O.jC) (h : O.Core) : Setup.Core { O with adm := adm } :=
  have ⟨x, P, h⟩ := h; ⟨x, P, h.1, h.2, h.3, h.4⟩

end GlobalTheory.Mean4O
