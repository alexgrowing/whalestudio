import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

section OrbitAlgSec

def TermCarC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ : (Y.cs u).Cl) (ρ' : (Y.cs u').Cl) (γ : X.B.I.GA), γ ∈ GamCol (Y.cs u) (Y.cs u') ρ ρ' →
      ∃ p : GCar X u u' (X.Fu u) (X.Fu u') ((Y.cs u).lamOf ρ) ((Y.cs u').lamOf ρ'), p.1.1 = γ

def StabNC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 →
      σ ∈ NLam ((Y.cs u').lamOf ρ') (lf D (X.Fu u'))

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem ratLink_fst_inj {x y : X.B.I.GA} {m n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m)
    (hy : RatLink X y n) (h : x.1 = y.1) : x = y := by
  obtain ⟨M, hMU, hM1, hM2, hM3⟩ := hx
  obtain ⟨N, hNU, hN1, hN2, hN3⟩ := hy
  obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace X.B.I.F))
  have hu := X.B.I.P_unit v
  have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [← h] at hN1
  have e0 := (hM1 v).symm.trans (hN1 v)
  have e1 := congrArg (fun Z => X.B.I.P v * Z * (X.B.I.P v)⁻¹) e0
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one] at e1
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul] at e1
  have eMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N :=
    Matrix.map_injective (X.B.I.φ v).injective e1
  have hy' : RatLink X y m := by
    refine ⟨M, hMU, fun w => ?_, ?_, hM3⟩
    · rw [← h]
      exact hM1 w
    · rw [hN2, eMN]
  exact Formalism.L2.SG.TermOp.Vanish.ratLink_unique X ⟨M, hMU, hM1, hM2, hM3⟩ hy'

theorem nlam_srat (w : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {x : X.B.I.GA}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n) (hn : n ∈ NLam Λ (lf D (X.Fu w))) :
    x ∈ Srat X w := by
  refine ⟨Formalism.L2.SG.TermOp.ratLink_mem X hx, Subgroup.subset_closure ⟨?_, ?_⟩⟩
  · have h1 := Formalism.L2.SG.Pf.nLamNinf_holds D X w Λ x n hx hn
    exact fun v => (h1 v).1
  · have h2 := Formalism.L2.SG.Pf.nLamNfin_holds D X w Λ x n hx hn
    exact ⟨h2.1, h2.2.1⟩

def ptL (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : X.B.I.GA :=
  if h : ∃ x : X.B.I.GA, RatLink X x n then h.choose else 1

theorem ptL_spec {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    RatLink X (ptL (X := X) n) n := by
  have h : ∃ x : X.B.I.GA, RatLink X x n := Formalism.L2.SG.Pf.ratPt_holds D X n hn
  unfold ptL
  rw [dif_pos h]
  exact h.choose_spec

theorem grel_equiv (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) :
    Equivalence (GRel X u u' F0 F0' Λ Λ') := by
  refine ⟨fun p => ⟨1, Formalism.L2.SG.Pf.nlam_one _ _, 1, Formalism.L2.SG.Pf.nlam_one _ _, by simp⟩, ?_, ?_⟩
  · rintro p q ⟨n, hn, n', hn', h⟩
    refine ⟨n⁻¹, Formalism.L2.SG.Pf.nlam_inv hn, n'⁻¹, Formalism.L2.SG.Pf.nlam_inv hn', ?_⟩
    rw [h]
    group
  · rintro p q s ⟨n, hn, n', hn', h⟩ ⟨m, hm, m', hm', h'⟩
    refine ⟨m * n, Formalism.L2.SG.Pf.nlam_mul hm hn, n' * m', Formalism.L2.SG.Pf.nlam_mul hn' hm', ?_⟩
    rw [h', h]
    simp only [mul_assoc]

theorem grel_out {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (p : GCar X u u' F0 F0' Λ Λ') :
    GRel X u u' F0 F0' Λ Λ' p (Quot.out (Quot.mk (GRel X u u' F0 F0' Λ Λ') p)) := by
  have h := Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u' F0 F0' Λ Λ') p))
  exact (grel_equiv u u' F0 F0' Λ Λ').symm ((Equivalence.eqvGen_iff (grel_equiv u u' F0 F0' Λ Λ')).1 h)

variable (Y : Full X) (u : D.what₂.Word)

def NOgrp (ρ : (Y.cs u).Cl) : Subgroup X.B.I.Ginf where
  carrier := NOcol (X.Fu u) (Y.cs u) ρ
  one_mem' := ⟨1, 1, ratLink_one X, rfl, Formalism.L2.SG.Pf.nlam_one _ _⟩
  mul_mem' := by
    rintro a b ⟨x, m, hx, rfl, hm⟩ ⟨y, n, hy, rfl, hn⟩
    exact ⟨x * y, m * n, Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hx hy, rfl, Formalism.L2.SG.Pf.nlam_mul hm hn⟩
  inv_mem' := by
    rintro a ⟨x, m, hx, rfl, hm⟩
    exact ⟨x⁻¹, m⁻¹, Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx, rfl, Formalism.L2.SG.Pf.nlam_inv hm⟩

def liftN (ρ : (Y.cs u).Cl) (y : X.B.I.Ginf) : X.B.I.GA :=
  if h : y ∈ NOcol (X.Fu u) (Y.cs u) ρ then h.choose else 1

theorem liftN_spec (ρ : (Y.cs u).Cl) {y : X.B.I.Ginf} (h : y ∈ NOcol (X.Fu u) (Y.cs u) ρ) :
    ∃ n, RatLink X (liftN Y u ρ y) n ∧ y = (liftN Y u ρ y).1 ∧ n ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := by
  have e : liftN Y u ρ y = h.choose := dif_pos h
  rw [e]
  exact h.choose_spec

theorem liftN_eq (ρ : (Y.cs u).Cl) {x : X.B.I.GA} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m)
    (hm : m ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))) : liftN Y u ρ x.1 = x := by
  have h : x.1 ∈ NOcol (X.Fu u) (Y.cs u) ρ := ⟨x, m, hx, rfl, hm⟩
  obtain ⟨n, hn, he, _⟩ := liftN_spec Y u ρ h
  exact ratLink_fst_inj hn hx he.symm

theorem orbitAlgC_of (hK : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) (hC : TermCarC) (hS : StabNC) : OrbitAlgC := by
  intro D X Y u u' hH ρ ρ'
  have hKg : X.LevelSubgroupCharacter := Y.hK
  let lift : NOgrp Y u ρ → X.B.I.GA := fun n => liftN Y u ρ (n : X.B.I.Ginf)
  have hsp : ∀ n : NOgrp Y u ρ, ∃ m, RatLink X (lift n) m ∧ (n : X.B.I.Ginf) = (lift n).1 ∧
      m ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := fun n => liftN_spec Y u ρ n.2

  have hlK : ∀ n : NOgrp Y u ρ,
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (lift n).2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 := by
    intro n
    obtain ⟨m, hm, -, hmN⟩ := hsp n
    exact (hK D X Y u ρ (lift n) m hmN hm).1
  refine ⟨NOgrp Y u ρ, lift, rfl, ?_, ?_, fun n => (hsp n).choose_spec.2.1.symm, ?_, ?_, ?_, hlK, ?_, ?_, ?_⟩
  ·
    refine Function.Injective.countable (f := fun n : NOgrp Y u ρ =>
      (⟨lift n, ratLink_mem X (hsp n).choose_spec.1⟩ : Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)) ?_
    intro a b hab
    have e : lift a = lift b := congrArg Subtype.val hab
    apply Subtype.ext
    calc (a : X.B.I.Ginf) = (lift a).1 := (hsp a).choose_spec.2.1
      _ = (lift b).1 := by rw [e]
      _ = b := (hsp b).choose_spec.2.1.symm
  ·
    have : Countable (GamCol (Y.cs u) (Y.cs u') ρ ρ') :=
      Function.Injective.countable (f := fun γ : GamCol (Y.cs u) (Y.cs u') ρ ρ' =>
        (⟨γ.1, γ.2.1⟩ : Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)) (fun a b h => Subtype.ext (congrArg (fun z : Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I => (z : X.B.I.GA)) h))
    infer_instance
  ·
    show liftN Y u ρ ((1 : X.B.I.GA).1) = 1
    exact liftN_eq Y u ρ (ratLink_one X) (Formalism.L2.SG.Pf.nlam_one _ _)
  ·
    intro n m
    obtain ⟨a, ha, hn1, haN⟩ := hsp n
    obtain ⟨b, hb, hm1, hbN⟩ := hsp m
    have e : ((n * m : NOgrp Y u ρ) : X.B.I.Ginf) = (lift n * lift m).1 := by
      show (n : X.B.I.Ginf) * m = (lift n).1 * (lift m).1
      rw [← hn1, ← hm1]
    show liftN Y u ρ ((n * m : NOgrp Y u ρ) : X.B.I.Ginf) = lift n * lift m
    rw [e]
    exact liftN_eq Y u ρ (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X ha hb) (Formalism.L2.SG.Pf.nlam_mul haN hbN)
  ·
    intro n
    obtain ⟨m, hm, -, hmN⟩ := hsp n
    exact nlam_srat u _ hm hmN
  ·
    intro c
    obtain ⟨p, hp⟩ := hC D X Y u u' hH ρ ρ' (ColCl.pt (Y.cs u) (Y.cs u') c) (Quotient.out c).2
    let t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
      ⟨_, (Y.cs u).lam_mem ρ, _, (Y.cs u').lam_mem ρ', Quot.mk _ p⟩
    obtain ⟨n, hn, n', hn', he⟩ := grel_out p
    have hxn : RatLink X (ptL n) n := ptL_spec hn.1.1
    have hxn' : RatLink X (ptL n') n' := ptL_spec hn'.1.1
    have htpt : t.pt = ptL n * p.1.1 * ptL n' := by
      have h1 : RatLink X t.pt t.lin := t.rep.2.1
      have h2 : RatLink X (ptL n * p.1.1 * ptL n') t.lin := by
        show RatLink X _ (Quot.out (Quot.mk _ p)).1.2
        rw [he]
        exact Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hxn p.2.1) hxn'
      exact Formalism.L2.SG.TermOp.Vanish.ratLink_unique X h1 h2
    have k1 := (hK D X Y u ρ (ptL n) n hn hxn).1
    have k2 := (hK D X Y u' ρ' (ptL n') n' hn' hxn').1
    have kγ : kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1 ∈ X.K2 := by
      rw [hp]; exact (Quotient.out c).2.2
    have hmem : ((ptL n)⁻¹ : X.B.I.GA).1 ∈ NOgrp Y u ρ :=
      ⟨(ptL n)⁻¹, n⁻¹, Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hxn, rfl, Formalism.L2.SG.Pf.nlam_inv hn⟩
    refine ⟨t, ⟨rfl, rfl, ?_⟩, ⟨((ptL n)⁻¹ : X.B.I.GA).1, hmem⟩, ?_⟩
    · rw [htpt]
      have e : kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) (ptL n * p.1.1 * ptL n') =
          ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (ptL n).2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
            kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1 *
            ((((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * (ptL n').2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')) := by
        simp only [kOf, Prod.snd_mul]; group
      rw [e]
      exact hKg.2.1 _ (hKg.2.1 _ k1 _ kγ) _ k2
    · have hl : lift ⟨((ptL n)⁻¹ : X.B.I.GA).1, hmem⟩ = (ptL n)⁻¹ :=
        liftN_eq Y u ρ (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hxn) (Formalism.L2.SG.Pf.nlam_inv hn)
      rw [hl, htpt, ← hp]
      have e : ((ptL n)⁻¹ * (ptL n * p.1.1 * ptL n'))⁻¹ * p.1.1 = (ptL n')⁻¹ := by group
      rw [e]
      exact (Srat X u').inv_mem (nlam_srat u' _ hxn' hn')
  ·
    intro t t' m ht ht' hs
    obtain ⟨Λ1, m1, Λ1', m1', c1⟩ := t
    obtain ⟨Λ2, m2, Λ2', m2', c2⟩ := t'
    obtain ⟨l1, l1', k1⟩ := ht
    obtain ⟨l2, l2', k2⟩ := ht'
    simp only at l1 l1' l2 l2'
    subst l1 l1' l2 l2'
    change kOf X u u' _ _ (Quot.out c1).1.1 ∈ X.K2 at k1
    change kOf X u u' _ _ (Quot.out c2).1.1 ∈ X.K2 at k2
    change (lift m * (Quot.out c1).1.1)⁻¹ * (Quot.out c2).1.1 ∈ Srat X u' at hs
    obtain ⟨nm, hnm, -, hnmN⟩ := hsp m
    set r1 := Quot.out c1 with hr1
    set r2 := Quot.out c2 with hr2
    have hRL : RatLink X ((lift m * r1.1.1)⁻¹ * r2.1.1) ((nm * r1.1.2)⁻¹ * r2.1.2) :=
      Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
        (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hnm r1.2.1)) r2.2.1
    have hiso : (nm * r1.1.2)⁻¹ * r2.1.2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hnmN.1.1 r1.2.2.1)) r2.2.2.1
    have hk : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * ((lift m * r1.1.1)⁻¹ * r2.1.1).2 *
        (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 := by
      have e : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * ((lift m * r1.1.1)⁻¹ * r2.1.1).2 *
          (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') =
          (kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) r1.1.1)⁻¹ *
            ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (lift m).2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u))⁻¹ *
            kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) r2.1.1 := by
        simp only [kOf, Prod.snd_mul, Prod.snd_inv]; group
      rw [e]
      exact hKg.2.1 _ (hKg.2.1 _ (hKg.2.2.1 _ k1) _ (hKg.2.2.1 _ (hlK m))) _ k2
    have hσ := hS D X Y u u' hH ρ' _ _ hRL hiso hs hk
    have hc : c1 = c2 := by
      rw [← Quot.out_eq c1, ← Quot.out_eq c2]
      exact Quot.sound ⟨nm, hnmN, (nm * r1.1.2)⁻¹ * r2.1.2, hσ, by
        show r2.1.2 = nm * r1.1.2 * ((nm * r1.1.2)⁻¹ * r2.1.2)
        group⟩
    subst hc
    rfl
  ·
    intro t ht
    ext y
    simp only [ROinf, ROset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, mm, hx, rfl, hmm, hconj⟩
      have hmm' : mm ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := ht.1 ▸ hmm
      have hmem : x.1 ∈ NOgrp Y u ρ := ⟨x, mm, hx, rfl, hmm'⟩
      refine ⟨⟨x.1, hmem⟩, rfl, ?_⟩
      have hl : lift ⟨x.1, hmem⟩ = x := liftN_eq Y u ρ hx hmm'
      rw [hl]
      have h3 := Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
        (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hx t.rep.2.1)) t.rep.2.1
      refine nlam_srat u' t.lam' h3 ?_
      have e : (mm * t.rep.1.2)⁻¹ * t.rep.1.2 = (t.lin⁻¹ * mm * t.lin)⁻¹ := by
        show (mm * t.lin)⁻¹ * t.lin = _
        group
      rw [e]
      exact Formalism.L2.SG.Pf.nlam_inv hconj
    · rintro ⟨n, rfl, hs⟩
      obtain ⟨nm, hnm, hn1, hnmN⟩ := hsp n
      refine ⟨lift n, nm, hnm, hn1, ht.1 ▸ hnmN, ?_⟩
      have hRL : RatLink X ((lift n * t.pt)⁻¹ * t.pt) ((nm * t.lin)⁻¹ * t.lin) :=
        Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
          (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hnm t.rep.2.1)) t.rep.2.1
      have hiso : (nm * t.lin)⁻¹ * t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hnmN.1.1 t.rep.2.2.1)) t.rep.2.2.1
      have hk : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * ((lift n * t.pt)⁻¹ * t.pt).2 *
          (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 := by
        have e : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * ((lift n * t.pt)⁻¹ * t.pt).2 *
            (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') =
            (kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) t.pt)⁻¹ *
              ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (lift n).2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u))⁻¹ *
              kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) t.pt := by
          simp only [kOf, Prod.snd_mul, Prod.snd_inv]; group
        rw [e]
        exact hKg.2.1 _ (hKg.2.1 _ (hKg.2.2.1 _ ht.2.2) _ (hKg.2.2.1 _ (hlK n))) _ ht.2.2
      have hσ := hS D X Y u u' hH ρ' _ _ hRL hiso hs hk
      have e : t.lin⁻¹ * nm * t.lin = ((nm * t.lin)⁻¹ * t.lin)⁻¹ := by group
      rw [e, ← ht.2.1]
      exact Formalism.L2.SG.Pf.nlam_inv hσ

end OrbitAlgSec

end Formalism.L2.SG.Pf.RegroupPf
