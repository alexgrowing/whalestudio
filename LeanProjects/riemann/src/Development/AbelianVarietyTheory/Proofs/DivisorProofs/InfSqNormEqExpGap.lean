import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApxGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSectionsCuspidal
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CovHt.Link.ApxAlg

theorem pn_eqRec {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv}
    (h : Δ = Δ') (m : C.Met Y σ Δ) : C.pn Y σ Δ' (h ▸ m) = C.pn Y σ Δ m := by
  subst h; rfl

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem pn_hodgeLw (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (la : AllWt.Weight S.Dw) :
    (cxSt D.what₂.LL).pn _ σ _ (DeKeyTrue.hodgeLw x Φ k σ la) =
      (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ (fun z => -exOf S.Dw la 0 (some z))) :=
  pn_eqRec _ _

theorem exOf_nsmul (u : AllWt.Weight S.Dw) (t : ℕ) :
    (fun z : Letter S.Dw => -exOf S.Dw (t • u) 0 (some z)) = t • fun z => -exOf S.Dw u 0 (some z) := by
  induction t with
  | zero =>
    funext z
    have h : exOf S.Dw 0 0 = 0 := by
      rw [exOf, wtOf_zero]; funext i; cases i <;> rfl
    simp [h]
  | succ t ih =>
    have h := exOf_add (t • u) u 0 0
    rw [add_zero] at h
    funext z
    have := congrFun ih z
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [succ_nsmul, h]
    simp only [Pi.add_apply]
    rw [neg_add, this]
    push_cast
    ring

end GlobalTheory.CovHt.Link.ApxAlg

namespace GlobalTheory.CovHt.Link.ApxAlg
open AlgebraicGeometry

theorem gen_pow {X : Scheme.{0}} [IsIntegral X] {Δ : CartierDiv X} {x : X} {f : X.functionField}
    (h : Δ.GeneratesAt x f) (t : ℕ) : (t • Δ).GeneratesAt x (f ^ t) := by
  obtain ⟨g, hg, hu⟩ := h
  exact ⟨g ^ t, hg.nsmul t, by rw [Units.val_pow_eq_pow_val, ← mul_pow]; exact ApproxSec.unitAt_pow hu t⟩

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem wtR_eq (L : CmList A) (u : AllWt.Weight S.Dw) :
    wtR L u = fun t i => ((u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ) : ℝ) := by
  funext t i; simp [wtR]

theorem gen_mbar (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw)
    (r : ℚ) (hr : 0 < r) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (y : Pts (Φ.C k).Y σ) (hy : y ∈ offBd Φ k σ) :
    (mbarOf P B (wtR L u) r k).D.GeneratesAt (under y)
      (genAt ((Φ.C k).Lw u) (under y) ^ ((mbarOf P B (wtR L u) r k).n : ℕ)) := by
  rw [wtR_eq, mbarOf_cast P B _ hr]
  have h := P.qDiv_mbarQ k B (fun t i => (u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ)) r
  rw [ApproxSec.qL_int] at h
  obtain ⟨a, m, ha, hm, h⟩ := ApproxSec.clear_den (PNat.pos _) hr h
  set M := P.mbarQ k B (fun t i => (u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ)) r with hM
  have hnorm : IsIntegrallyClosed ((Φ.C k).Y.X.presheaf.stalk (under y)) :=
    (have := (Φ.C k).Y.isNormalScheme; inferInstance)
  have hd := Base.isEqn_eqn M.D (under y)
  have hb := Base.isEqn_eqn (P.bd k) (under y)
  have hγ := Base.isEqn_eqn ((Φ.C k).Lw u) (under y)
  have hbu : UnitAt (under y) (eqn (P.bd k) (under y) : (Φ.C k).Y.Fn) := by
    by_contra hc
    exact hy ((P.mem_supp_bd k (under y)).1 (hb.mem_supp_iff.2 hc))
  have h1 := (hd.nsmul a).add (hb.nsmul m)
  rw [h] at h1
  have h2 := (hγ.nsmul ((M.n : ℕ) * a)).iff_unitAt.1 h1
  rw [hd.generatesAt_iff]
  have hw0 : genAt ((Φ.C k).Lw u) (under y) ^ (M.n : ℕ) * (eqn M.D (under y) : (Φ.C k).Y.Fn) ≠ 0 := by
    simp [genAt]
  have hwa : UnitAt (under y) ((genAt ((Φ.C k).Lw u) (under y) ^ (M.n : ℕ) *
      (eqn M.D (under y) : (Φ.C k).Y.Fn)) ^ a) := by
    have e : (genAt ((Φ.C k).Lw u) (under y) ^ (M.n : ℕ) * (eqn M.D (under y) : (Φ.C k).Y.Fn)) ^ a =
        (((eqn M.D (under y) ^ a * eqn (P.bd k) (under y) ^ m : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) /
          (eqn ((Φ.C k).Lw u) (under y) ^ ((M.n : ℕ) * a) : (Φ.C k).Y.Fnˣ)) *
          ((eqn (P.bd k) (under y) : (Φ.C k).Y.Fn) ^ m)⁻¹ := by
      have := (eqn (P.bd k) (under y)).ne_zero
      have := (eqn ((Φ.C k).Lw u) (under y)).ne_zero
      simp only [genAt, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, inv_pow, ← pow_mul]
      field_simp
    rw [e]
    exact h2.mul (ApproxSec.unitAt_pow hbu m).inv
  rw [unitAt_iff hw0]
  refine ⟨ApproxSec.regAt_of_pow hnorm ha hwa.regAt, ApproxSec.regAt_of_pow hnorm ha ?_⟩
  rw [inv_pow]
  exact hwa.inv.regAt

end GlobalTheory.CovHt.Link.ApxAlg

namespace GlobalTheory.CovHt.Link.ApxAlg
open AlgebraicGeometry

theorem real_alg (A P Q : ℝ) (n τ : ℕ) (hA : 0 ≤ A) (hP : 0 < P) (hQ : 0 < Q) (hn : 0 < n) :
    A ^ 2 * P ^ τ = (Real.exp (-((τ : ℝ) * 0)) * ((A ^ n) ^ 2 * Q ^ τ) ^ (1 / (2 * (n : ℝ)))) ^ 2 *
      Real.exp (2 * τ * (Real.log P / 2 - Real.log Q / 2 / n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have e1 : ((A ^ n) ^ 2) ^ (1 / (2 * (n : ℝ))) = A := by
    rw [← pow_mul, show 1 / (2 * (n : ℝ)) = ((n * 2 : ℕ) : ℝ)⁻¹ by push_cast; ring]
    exact Real.pow_rpow_inv_natCast hA (by omega)
  have e2 : (Q ^ τ) ^ (1 / (2 * (n : ℝ))) = Real.exp (τ * Real.log Q / (2 * n)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
    ring_nf
  have e3 : P ^ τ = Real.exp (τ * Real.log P) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hP τ)]
  rw [e1, e2, e3, mul_zero, neg_zero, Real.exp_zero, one_mul, mul_pow, ← Real.exp_nat_mul, mul_assoc,
    ← Real.exp_add]
  congr 2
  field_simp
  push_cast
  ring

theorem ratVal_pow' {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {y : Pts Y σ} {a : Y.Fn}
    (ha : RegAt (under y) a) (n : ℕ) : ratVal (a ^ n) y = ratVal a y ^ n := by
  induction n with
  | zero => simp [Base.ratVal_one]
  | succ n ih => rw [pow_succ, pow_succ, ratVal_mul (ApproxSec.regAt_pow ha n) ha, ih]

theorem pos_of_gen {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}
    {m : C.Met Y σ Δ} {y : Pts Y σ} {f : Y.Fn} (h : PosAt m y) (hf : Δ.GeneratesAt (under y) f) :
    0 < C.pn Y σ Δ m (C.cx Y σ f) y := by
  obtain ⟨c, hc, e⟩ := exists_pn_eq (C := C) hf
  rw [e m]
  exact mul_pos hc h

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem divOf_nsmul' (Φ : s.Flag) (k : s.Comp) (e : Letter S.Dw → ℤ) (t : ℕ) :
    divOf (Φ.C k) (t • e) = t • divOf (Φ.C k) e := by
  simp [divOf, Finset.smul_sum, mul_smul]

theorem pn_metsOf_pow (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (e : Letter S.Dw → ℤ)
    (y : Pts (Φ.C k).Y σ) (g : (Φ.C k).Y.Fn) (hg : (divOf (Φ.C k) e).GeneratesAt (under y) g) (t : ℕ) (ht : 1 ≤ t) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ (t • e)) ((cxSt D.what₂.LL).cx _ σ (g ^ t)) y =
      (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ e) ((cxSt D.what₂.LL).cx _ σ g) y ^ t := by
  induction t, ht using Nat.le_induction with
  | base => rw [pow_one, pow_one, one_nsmul]
  | succ t ht ih =>
    have h1 : (divOf (Φ.C k) (t • e)).RegularAt (under y) (g ^ t) := by
      rw [divOf_nsmul']; exact (gen_pow hg t).regularAt
    rw [succ_nsmul, pn_metsOf_add, pow_succ, pow_succ,
      (cxSt D.what₂.LL).pn_mAdd _ _ _ _ _ _ _ _ _ h1 hg.regularAt, ih]

end GlobalTheory.CovHt.Link.ApxAlg

namespace GlobalTheory.CovHt.Link.ApxAlg
open AlgebraicGeometry

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem reg_mbar (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw)
    (r : ℚ) (hr : 0 < r) (k : s.Comp) (τ : ℕ) (hτ : 1 ≤ τ) (f : (Φ.C k).Y.Fn)
    (hf : f ∈ (mbarOf P B (wtR L u) r k).secs τ) (z : (Φ.C k).Y.X) :
    (τ • (Φ.C k).Lw u).RegularAt z f := by
  rw [wtR_eq, mbarOf_cast P B _ hr] at hf
  have h := P.qDiv_mbarQ k B (fun t i => (u (L.ψ t) (Fin.cast S.rank_eq.symm i) : ℚ)) r
  rw [ApproxSec.qL_int] at h
  obtain ⟨a, m, ha, hm, h⟩ := ApproxSec.clear_den (PNat.pos _) hr h
  exact (ApproxSec.local_sec (x := z) (have := (Φ.C k).Y.isNormalScheme; inferInstance) ha hm (PNat.pos _) hτ h
    (P.eff_bd k) (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hf z)).1

theorem ci_mbarOf (Φ : s.Flag) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : D.what₂.Tau → Fin N → ℝ) (r : ℚ)
    (k : s.Comp) : (mbarOf P B u r k).ci = 0 := by
  unfold mbarOf
  split_ifs <;> rfl

end GlobalTheory.CovHt.Link.ApxAlg

namespace GlobalTheory.CovHt.Link

open GlobalTheory.CovHt.Link.ApxAlg in

theorem infSq_eq_nrmInf_mul_exp : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (r : ℚ), 0 < r → ∀ (k : s.Comp) (τ : ℕ), 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, ∀ (σ : D.what₂.LL →+* ℂ), ∀ y ∈ offBd Φ k σ, infSq Φ k x (τ • u) σ f y = (mbarOf P B (wtR L u) r k).nrmInf σ τ f y ^ 2 * Real.exp (2 * τ * apxGap Φ L x P B u r k σ y) := by
  intro D A N j S κ s Φ L x P B u r hr k τ hτ f hf σ y hy
  have hgen := gen_mbar Φ L x P B u r hr k σ y hy
  have hreg := reg_mbar Φ L x P B u r hr k τ hτ f hf (under y)
  have hγ := (Base.isEqn_eqn ((Φ.C k).Lw u) (under y)).nsmul τ
  obtain ⟨a, ha, rfl⟩ : ∃ a : (Φ.C k).Y.Fn, RegAt (under y) a ∧ f = a * genAt ((Φ.C k).Lw u) (under y) ^ τ := by
    refine ⟨_, hγ.regularAt_iff.1 hreg, ?_⟩
    have := (eqn ((Φ.C k).Lw u) (under y)).ne_zero
    simp only [genAt, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
    field_simp
  set e : Letter S.Dw → ℤ := fun z => -exOf S.Dw u 0 (some z) with he
  have hΛ : divOf (Φ.C k) e = (Φ.C k).Lw u := DeKeyTrue.divOf_neg_exOf Φ k u
  have hg : (divOf (Φ.C k) e).GeneratesAt (under y) (genAt ((Φ.C k).Lw u) (under y)) :=
    hΛ ▸ generatesAt_genAt _ _
  have hregg : ((Φ.C k).Lw (τ • u)).RegularAt (under y) (genAt ((Φ.C k).Lw u) (under y) ^ τ) := by
    rw [ApproxSec.Lw_nsmul]; exact (gen_pow (generatesAt_genAt _ _) τ).regularAt
  have hP : 0 < (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ e)
      ((cxSt D.what₂.LL).cx _ σ (genAt ((Φ.C k).Lw u) (under y))) y :=
    pos_of_gen (posAt_of_posSet (posSet_metsOf x Φ k none σ e) y) hg
  have hu : ∀ τ i, ∃ q : ℚ, wtR L u τ i = q := fun τ i => ⟨_, congrFun (congrFun (wtR_eq L u) τ) i⟩
  obtain ⟨_q, _b, _hq, _hc, _hD, hpos, _hfin⟩ := isComb_mbarOf P B hu hr k
  have hQ := pos_of_gen (hpos σ y).1 hgen
  have hL : infSq Φ k x (τ • u) σ (a * genAt ((Φ.C k).Lw u) (under y) ^ τ) y = ‖ratVal a y‖ ^ 2 *
      (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ e)
        ((cxSt D.what₂.LL).cx _ σ (genAt ((Φ.C k).Lw u) (under y))) y ^ τ := by
    unfold infSq
    rw [(cxSt D.what₂.LL).pn_mul _ _ _ _ _ _ _ ha hregg, pn_hodgeLw, exOf_nsmul, ← he,
      pn_metsOf_pow x Φ k σ e y _ hg τ hτ]
  have hR : (mbarOf P B (wtR L u) r k).nrmInf σ τ (a * genAt ((Φ.C k).Lw u) (under y) ^ τ) y =
      Real.exp (-((τ : ℝ) * 0)) * ((‖ratVal a y‖ ^ ((mbarOf P B (wtR L u) r k).n : ℕ)) ^ 2 *
        (cxSt D.what₂.LL).pn _ σ _ ((mbarOf P B (wtR L u) r k).m σ) ((cxSt D.what₂.LL).cx _ σ
          (genAt ((Φ.C k).Lw u) (under y) ^ ((mbarOf P B (wtR L u) r k).n : ℕ))) y ^ τ) ^
        (1 / (2 * (((mbarOf P B (wtR L u) r k).n : ℕ) : ℝ))) := by
    rw [Adl.nrmInf, ci_mbarOf]
    have e1 : (a * genAt ((Φ.C k).Lw u) (under y) ^ τ) ^ ((mbarOf P B (wtR L u) r k).n : ℕ) =
        a ^ ((mbarOf P B (wtR L u) r k).n : ℕ) *
          (genAt ((Φ.C k).Lw u) (under y) ^ ((mbarOf P B (wtR L u) r k).n : ℕ)) ^ τ := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm τ]
    rw [e1, (cxSt D.what₂.LL).pn_mul _ _ _ _ _ _ _ (ApproxSec.regAt_pow ha _) (gen_pow hgen τ).regularAt,
      (cxSt D.what₂.LL).pn_mPow _ _ _ _ _ _ _ hgen, ratVal_pow' ha, norm_pow]
    rfl
  rw [hL, hR, apxGap, lnN, lnN, pn_hodgeLw, ← he]
  exact real_alg _ _ _ _ _ (norm_nonneg _) hP hQ (PNat.pos _)

end GlobalTheory.CovHt.Link
