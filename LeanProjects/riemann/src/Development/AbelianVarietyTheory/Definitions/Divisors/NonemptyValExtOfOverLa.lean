import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawLogarithm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVR
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartLocalDepthLeOfValuedExtensionBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdDetMemHaO
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FactorDepth

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.LawLog

section Log

open MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

def logFGLOf (v : AddValuation C (WithTop ℝ)) (G : FGLaw C d)
    (hG : ∀ a, MvIsInt v (subst (twoVars C d) (G.F a))) : LogFGL v d where
  lg a := subst (oneVar C d) (GlobalTheory.FormalLog.logOf G a)
  lg_const a := constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (GlobalTheory.FormalLog.constantCoeff_prim _)
  lg_lin a b := by
    rw [coeff_single_oneVar]
    have h := congrArg constantCoeff (GlobalTheory.FormalLog.pderiv_logOf G a b)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (GlobalTheory.FormalLog.cc_om G) a) b
    simp only [Matrix.map_apply, Matrix.one_apply] at h2
    simpa [h2] using h
  F a := subst (twoVars C d) (G.F a)
  F_int := hG
  F_const a := constantCoeff_subst_eq_zero hs_twoVars cc_twoVars (G.const a)
  lg_F a := by
    have hp : ∀ (j : Fin 2) i, constantCoeff (pt C (n := 2) d j i) = 0 := fun j i => by simp [pt]
    have e0 : (fun b => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
        fun i => subst (twoVars C d) (pt C (n := 2) d 0 i) := by
      funext i; rw [pt, subst_X hs_twoVars]; simp [twoVars]
    have e1 : (fun b => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
        fun i => subst (twoVars C d) (pt C (n := 2) d 1 i) := by
      funext i; rw [pt, subst_X hs_twoVars]; simp [twoVars]
    rw [e0, e1, subst_oneVar _ cc_twoVars _ G.const, subst_oneVar _ cc_twoVars _ (hp 0),
      subst_oneVar _ cc_twoVars _ (hp 1), ← subst_add hs_twoVars]
    congr 1
    exact GlobalTheory.FormalLog.logOf_add G a

end Log

section Val

variable {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem log_v_p_neg : Real.log (X.v (p : X.C) : ℝ) < 0 := by
  have hp0 : (p : X.C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpos : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
    have : X.v (p : X.C) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hle : X.v (p : X.C) ≤ 1 := by
    have := X.ints.map_le_one (p : X.O)
    rwa [map_natCast] at this
  have hne : X.v (p : X.C) ≠ 1 := fun h =>
    X.nonunit.out (X.ints.isUnit_of_one' (by rwa [map_natCast]))
  exact Real.log_neg hpos (by exact_mod_cast lt_of_le_of_ne hle hne)

def vX_vp : AddValuation X.C (WithTop ℝ) :=
  (exists_addValuation_mul_log X.v (Real.log (X.v (p : X.C) : ℝ))⁻¹ (inv_lt_zero.2 (log_v_p_neg X))).choose

theorem vX_vp_apply {x : X.C} (hx : x ≠ 0) :
    vX_vp X x = (((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v x : ℝ) : ℝ) : WithTop ℝ) :=
  (exists_addValuation_mul_log X.v _ (inv_lt_zero.2 (log_v_p_neg X))).choose_spec x hx

theorem vX_vp_p : vX_vp X (p : X.C) = 1 := by
  rw [vX_vp_apply X (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero), inv_mul_cancel₀ (log_v_p_neg X).ne]
  rfl

theorem isIntV_iff (x : X.C) : IsIntV (vX_vp X) x ↔ X.v x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp [IsIntV]
  have hpos : (0 : ℝ) < (X.v x : ℝ) := by
    have : X.v x ≠ 0 := by simpa using hx
    exact_mod_cast pos_iff_ne_zero.2 this
  have hl := inv_lt_zero.2 (log_v_p_neg X)
  have h1 : Real.log (X.v x : ℝ) ≤ 0 ↔ X.v x ≤ 1 := by
    rw [Real.log_nonpos_iff hpos.le]; exact_mod_cast Iff.rfl
  rw [IsIntV, vX_vp_apply X hx, ← WithTop.coe_zero, WithTop.coe_le_coe, ← h1]
  exact ⟨fun h => by by_contra hn; nlinarith [mul_pos_of_neg_of_neg hl (neg_neg_of_pos (not_le.1 hn))],
    fun h => mul_nonneg_of_nonpos_of_nonpos hl.le h⟩

def jX : T.V →+* X.C := X.ιF.comp (algebraMap T.V T.Fr)

theorem isIntV_jX (r : T.V) : IsIntV (vX_vp X) (jX X r) := by
  rw [isIntV_iff, jX, RingHom.comp_apply, X.comp]
  exact X.ints.map_le_one _

theorem vX_vp_jX_unit {r : T.V} (hr : IsUnit r) : vX_vp X (jX X r) = 0 := by
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  have h : vX_vp X (jX X r) + vX_vp X (jX X s) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, hs, map_one, AddValuation.map_one]
  exact le_antisymm (h ▸ le_add_of_nonneg_right (isIntV_jX X s)) (isIntV_jX X r)

theorem vX_vp_ιF {x : T.Fr} (hx : x ≠ 0) :
    vX_vp X (X.ιF x) = (((vV T.V x : ℝ) / (vV T.V (p : T.Fr) : ℝ) : ℝ) : WithTop ℝ) := by
  have hpos : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
    have : X.v (p : X.C) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  rw [vX_vp_apply X ((map_ne_zero X.ιF).2 hx), X.val x hx, Real.log_rpow hpos]
  congr 1
  have := (log_v_p_neg X).ne
  field_simp

theorem toE_vX_vp_ιF {e : ℕ} (he : vV T.V (p : T.Fr) = e) (x : T.Fr) :
    toE (vX_vp X (X.ιF x)) = nval T.V e x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, nval_zero, AddValuation.map_zero]; rfl
  rw [vX_vp_ιF X hx, nval_of_ne hx, he]; rfl

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Exponents

abbrev rk (f : Lt1 Dw) : ℕ := f.2.val + 1

theorem rk_le (f : Lt1 Dw) : rk f ≤ Dw.mult f.1 := f.2.isLt

def gap (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (f : Lt1 Dw) : ℕ :=
  a (f.1, f.2.val) - if rk f < Dw.mult f.1 then a (f.1, rk f) else 0

def degP (cx : Lt1 Dw → ℕ) : ℕ := ∑ f, rk f * cx f

theorem sum_gap_tail (g : ℕ → ℕ) (hg : Antitone g) (m i : ℕ) (hi : i < m) :
    ∑ j ∈ Finset.range m, (if i < j + 1 then g j - (if j + 1 < m then g (j + 1) else 0) else 0) = g i := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have key : ∀ n, i ≤ n → ∑ j ∈ Finset.range n, (if i < j + 1 then g j - g (j + 1) else 0) + g n = g i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [Finset.sum_eq_zero fun j hj => if_neg (by have := Finset.mem_range.1 hj; omega), zero_add]
    | succ n hn ih =>
      have := hg (Nat.le_succ n)
      rw [Finset.sum_range_succ, if_pos (by omega), ← ih]
      simp only [Nat.succ_eq_add_one] at this
      omega
  rw [Finset.sum_range_succ, if_pos hi, if_neg (lt_irrefl _), Nat.sub_zero, ← key k (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_pos (show j + 1 < k + 1 by have := Finset.mem_range.1 hj; omega)]

open Classical in

theorem sum_gap_row {a : (E →+* ℂ) × ℕ → ℕ} (ha : ∀ τ, Antitone fun i => a (τ, i)) (τ : E →+* ℂ)
    (i : Fin (Dw.mult τ)) :
    ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => f.1 = τ ∧ i.val < rk f), gap Dw a f = a (τ, i) := by
  rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single τ]
  · rw [← sum_gap_tail (fun i => a (τ, i)) (ha τ) (Dw.mult τ) i i.isLt, ← Fin.sum_univ_eq_sum_range
      (fun j => if i.val < j + 1 then a (τ, j) - (if j + 1 < Dw.mult τ then a (τ, j + 1) else 0) else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [true_and, gap, rk]
  · intro σ _ hσ
    exact Finset.sum_eq_zero fun j _ => if_neg fun h => hσ h.1
  · intro h; exact absurd (Finset.mem_univ τ) h

def prodP (C : Type) [Field C] (cx : Lt1 Dw → ℕ) :
    MvPolynomial (Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1)) C :=
  ∏ f : Lt1 Dw, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f), Fin (rk f)) =>
    (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (detPow C (rk f) (cx f))

end Exponents

variable {Xo : Moduli Dw l} {c : Coeff l}

section Chart

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
  {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def lawX : FGLaw X.C (chD Ch.ch) := letI := io.toAlgebra; GlobalTheory.FBMap.mapLaw X.ιF Ch.ch.B.G

theorem lawX_F (a : Fin (chD Ch.ch)) : (lawX Ch X).F a = MvPowerSeries.map (jX X) (Ch.FT a) := by
  let _ := io.toAlgebra
  show MvPowerSeries.map X.ιF (Ch.ch.B.G.F a) = _
  rw [Ch.gen.1.1 a, jX, MvPowerSeries.map_comp]; rfl

def fgl : LogFGL (vX_vp X) (chD Ch.ch) :=
  logFGLOf (vX_vp X) (lawX Ch X) fun a α => by
    have e : MvPowerSeries.subst (twoVars X.C _) ((lawX Ch X).F a) =
        MvPowerSeries.map (jX X) (MvPowerSeries.subst (twoVars T.V _) (Ch.FT a)) := by
      rw [lawX_F, MvPowerSeries.map_subst hs_twoVars]
      congr 1
      funext q
      simp [twoVars]
    rw [e, MvPowerSeries.coeff_map]
    exact isIntV_jX X _

theorem fgl_F (a : Fin (chD Ch.ch)) :
    (fgl Ch X).F a = MvPowerSeries.subst (twoVars X.C _) (MvPowerSeries.map (jX X) (Ch.FT a)) := by
  rw [← lawX_F]; rfl

def actX (a : 𝓞 E) : Fin (chD Ch.ch) → MvPowerSeries (Fin (chD Ch.ch)) X.C :=
  fun i => MvPowerSeries.subst (oneVar X.C _) (MvPowerSeries.map (jX X) (Ch.actT a i))

def lieVec (ℓ : Lt1 Dw) : Fin (chD Ch.ch) → X.C := fun e => jX X (Ch.uvecT ℓ e)

def frame (f : Lt1 Dw) : Fin (rk f) → Fin (chD Ch.ch) → X.C :=
  fun a => lieVec Ch X ⟨f.1, Fin.castLE (rk_le f) a⟩

theorem exists_unit_minor {R : Type} [CommRing R] [IsLocalRing R] {i d : ℕ} (U : Matrix (Fin i) (Fin d) R)
    (S : Matrix (Fin d) (Fin i) R) (h : U * S = 1) :
    ∃ r : Fin i → Fin d, IsUnit (Matrix.of fun a b => U a (r b)).det := by
  by_contra hn
  push Not at hn
  have e : (U * S).det = ∑ r : Fin i → Fin d, (Matrix.of fun a b => U a (r b)).det * ∏ k, S (r k) k := by
    simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
      Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  have hm : (U * S).det ∈ maximalIdeal R := by
    rw [e]
    exact Ideal.sum_mem _ fun r _ => Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 (hn r))
  rw [h, Matrix.det_one] at hm
  exact (mem_maximalIdeal _).1 hm isUnit_one

theorem isSatFrame_frame (f : Lt1 Dw) : IsSatFrame (vX_vp X) (frame Ch X f) := by
  refine ⟨fun a e => isIntV_jX X _, ?_⟩
  obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := chart_saturated T io y Ch f.1
  choose s hs using fun e : Fin (chD Ch.ch) => (hb (Pi.single e 1)).exists
  have h1 : Matrix.of s * Matrix.of w = 1 := by
    ext e j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Pi.single_apply, eq_comm] using hs e j
  have h2 : Matrix.of w * Matrix.of s = 1 := mul_eq_one_comm.1 h1
  obtain ⟨r, hr⟩ := exists_unit_minor
    (Matrix.of fun (a : Fin (rk f)) e => Ch.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩ e)
    (Matrix.of fun e (b : Fin (rk f)) => s e (emb (Fin.castLE (rk_le f) b))) (by
      ext a b
      have h3 := congrFun (congrFun h2 (emb (Fin.castLE (rk_le f) a))) (emb (Fin.castLE (rk_le f) b))
      simp only [Matrix.mul_apply, Matrix.of_apply, hw, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq,
        Fin.castLE_inj] at h3 ⊢
      exact h3)
  refine ⟨r, ?_⟩
  rw [← vX_vp_jX_unit X hr, RingHom.map_det]
  rfl

def nuFacC (f : Lt1 Dw) (k : ℕ) : EReal := detDepth (fgl Ch X) (frame Ch X f) k

def nuProdC (cx : Lt1 Dw → ℕ) : EReal :=
  depth (fun _ : (Σ f : Lt1 Dw, Fin (rk f)) => fgl Ch X) (fun b => frame Ch X b.1) (prodP X.C cx)

def nuLocOf (e k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) T.Fr) : EReal :=
  letI := io.toAlgebra
  ⨅ (f : PS T.Fr n Ch.ch.d) (_ : IsIntPS T f),
    letI := io.toAlgebra
    nval T.V e (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)

theorem nuLocC_eq_iInf (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    nuLocC Ch e k a n = ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n), nuLocOf Ch e k P :=
  rfl

end Chart

section Point

variable [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io)

def nuFac (f : Lt1 Dw) (k : ℕ) : EReal :=
  ⨅ (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), nuFacC Ch X f k

def nuP (cx : Lt1 Dw → ℕ) : EReal := ∑ f, nuFac p y f (cx f)

def nuProd (cx : Lt1 Dw → ℕ) : EReal :=
  ⨅ (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), nuProdC Ch X cx

variable {p y}

theorem nuFac_le (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ) :
    nuFac p y f k ≤ nuFacC Ch X f k :=
  iInf_le_of_le Ch (iInf_le _ X)

theorem le_nuFac {f : Lt1 Dw} {k : ℕ} {r : EReal}
    (h : ∀ (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), r ≤ nuFacC Ch X f k) : r ≤ nuFac p y f k :=
  le_iInf₂ h

omit [StarRing (𝓞 E)] in

theorem not_isUnit_of_overLa (la : PointsOfFlagModel.abelian₂ p c) {e : ℕ} (ho : OverLa la.1 T.V io e) : ¬ IsUnit (p : T.V) := by
  intro hu
  have hp0 : (p : 𝓞 c.F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : la.1.valuation c.F (p : c.F) < 1 := by
    have := (la.1.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 la.2
    simpa using this
  have h0 : la.1.valuation c.F (p : c.F) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have h2 : 0 < vLa la.1 (p : c.F) := by
    unfold vLa
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    omega
  have h3 := ho.2 (p : c.F)
  rw [map_natCast] at h3
  have h4 : valV T.V (p : T.Fr) = 1 := by
    have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := T.Fr)
      (IsDiscreteValuationRing.maximalIdeal T.V) (r := (p : T.V))).2 fun h => (mem_maximalIdeal _).1 h hu
    rwa [map_natCast] at this
  have h5 : vV T.V (p : T.Fr) = 0 := by simp [vV, h4]
  have h6 : (0 : ℤ) < e := by exact_mod_cast ho.1
  nlinarith [mul_pos h6 h2]

omit [StarRing (𝓞 E)] in

theorem nonempty_valExt_of_overLa (la : PointsOfFlagModel.abelian₂ p c) {e : ℕ} (ho : OverLa la.1 T.V io e) : Nonempty (ValExt T p) :=
  nonempty_valExt T p (not_isUnit_of_overLa la ho)

end Point

section Columns

def polyP {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    MvPolynomial (LtN Dw n) k :=
  ∏ f : Lt1 Dw, (GlobalTheory.CombMinor.cMat (r := Dw.mult) f.1 (rk f) (rk_le f) (B f)).det ^ cx f

def IsIsoCols (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) (τ : E →+* ℂ) {i n : ℕ} (S : Set (Fin n))
    (B : Fin i → Fin n → T.V) : Prop :=
  (∀ b j, j ∉ S → B b j = 0) ∧
  (∃ r : Fin i → Fin n, IsUnit (Matrix.of fun b b' => B b (r b')).det) ∧
  ∀ N : ℕ, ∃ x : Fin i → Fin n → 𝓞 E, (∀ b j, j ∉ S → x b j = 0) ∧
    (∀ b j, ∃ z : T.V, io (embK c τ (x b j)) = algebraMap T.V T.Fr (B b j + (p : T.V) ^ N * z)) ∧
    ∀ b b', ∑ j, x b j * H.bar (x b' j) ∈ Ideal.span {(p : 𝓞 E) ^ N}

def IsCols (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) (cx : Lt1 Dw → ℕ) {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) : Prop :=
  ∃ blk : (Σ f : {f : Lt1 Dw // cx f ≠ 0}, Fin (2 * rk f.1)) ↪ Fin n,
    ∀ f : {f : Lt1 Dw // cx f ≠ 0}, IsIsoCols c T io p f.1.1 (Set.range fun j => blk ⟨f, j⟩) (B f.1)

def polyT {T : CDVR} {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (cx : Lt1 Dw → ℕ) :
    MvPolynomial (LtN Dw n) T.Fr :=
  polyP (fun f b j => algebraMap T.V T.Fr (B f b j)) cx

theorem polyT_mem_FFV {T : CDVR} {io : c.F →+* T.Fr} {p n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    (ha : ∀ τ, Antitone fun i => a (τ, i)) {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V}
    (hB : IsCols c T io p (gap Dw a) B) : polyT B (gap Dw a) ∈ FFV (Dw := Dw) T a n := by
  obtain ⟨blk, hb⟩ := hB
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ := fun τ h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ h
  refine GlobalTheory.CombMinor.prod_det_mem_HaO (E →+* ℂ) Dw.mult n T.Fr _ _ _ _ (Lt1 Dw) (fun f => f.1) rk rk_le _ _
    (fun f b j => ⟨_, rfl⟩) hcc (fun f f' hf hf' h b b' j => ?_) (fun τ i => ?_)
  · by_contra hn
    push Not at hn
    have h1 : j ∈ Set.range fun j => blk ⟨⟨f, hf⟩, j⟩ := by
      by_contra hj
      exact hn.1 (by rw [(hb ⟨f, hf⟩).1 b j hj, map_zero])
    have h2 : j ∈ Set.range fun j => blk ⟨⟨f', hf'⟩, j⟩ := by
      by_contra hj
      exact hn.2 (by rw [(hb ⟨f', hf'⟩).1 b' j hj, map_zero])
    obtain ⟨j1, h1⟩ := h1
    obtain ⟨j2, h2⟩ := h2
    have h3 : f = f' := congrArg (fun s => s.1.1) (blk.injective (h1.trans h2.symm))
    subst h3
    exact hcc _ h.symm
  · convert sum_gap_row (Dw := Dw) ha τ i

theorem nuLocC_le_nuLocOf [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (Ch : IntegralChartA3 Xo c T io y) (e k : ℕ) {p n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    (ha : ∀ τ, Antitone fun i => a (τ, i)) {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V}
    (hB : IsCols c T io p (gap Dw a) B) : nuLocC Ch e k a n ≤ nuLocOf Ch e k (polyT B (gap Dw a)) := by
  rw [nuLocC_eq_iInf]
  exact iInf₂_le _ (polyT_mem_FFV ha hB)

end Columns

section Generic

def dimFlag (Dw : Datum H) : ℕ := Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2

variable {O : Type} [CommRing O] {β : O →+* c.F} {T : CDVR} {io : c.F →+* T.Fr}

def ptF (y : IntFr Xo c T io) : Sp T.Fr ⟶ Xo.XF c :=
  letI := io.toAlgebra; CompSplitPfB.cspB_lift y.1.x y.1.x_over

def OnComp (Z : Comp Xo c) (y : IntFr Xo c T io) : Prop := ∀ q, ptF y q ∈ (Z : Set (Xo.XF c))

def IsExtension (Y : Model Xo c β) (y : IntFr Xo c T io) (yt : Sp T.V ⟶ Y.X)
    (ut : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left)) : Prop :=
  letI := io.toAlgebra
  spMap (algebraMap T.V T.Fr) ≫ yt = ptF y ≫ Y.j ∧ (∀ τ i, IsTanAtG Y.t yt (ut τ i)) ∧
    ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left,
      u' ≫ Y.oF.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ ptF y ∧
      u' ≫ Y.m0.toSABMap.φ = y.1.u τ i ∧
      u' ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ ut τ i

def FlagsDefinedOver {X0 : Scheme.{0}} (t : SAB H X0) {k : Type} [Field k] (x : Sp k ⟶ X0)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber k) ⟶ t.G.left)) {k' : Type} [Field k'] (φ : k' →+* k) :
    Prop :=
  ∃ (x' : Sp k' ⟶ X0) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber k') ⟶ t.G.left)),
    spMap φ ≫ x' = x ∧ (∀ τ j, IsTanAtG t x' (v τ j)) ∧
    ∀ τ i, ∃ cf : Fin (Dw.mult τ) → k, (∀ j, i < j → cf j = 0) ∧
      IsCombAtG t x (fun j => spMap (dualMap φ) ≫ v τ j) cf (u τ i)

def TrdegGe (k : Type) [Field k] (n : ℕ) : Prop :=
  ∃ t : Fin n → k, AlgebraicIndependent (⊥ : Subfield k) t

def IsGen (Y : Model Xo c β) (y : IntFr Xo c T io) : Prop :=
  ∃ (yt : Sp T.V ⟶ Y.X) (ut : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left)),
    IsExtension Y y yt ut ∧
    ∀ (k' : Type) [Field k'] (φ : k' →+* ResidueField T.V),
      FlagsDefinedOver (Dw := Dw) Y.t (spMap (residue T.V) ≫ yt)
        (fun τ i => spMap (dualMap (residue T.V)) ≫ ut τ i) φ →
      TrdegGe k' (dimFlag Dw)

def GenEx (Y : Model Xo c β) (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (y : IntFr Xo c T io), OnComp Z y ∧ IsGen Y y

attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in

theorem isTanAtG_map {X0 : Scheme.{0}} (t : SAB H X0) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {x : Sp S ⟶ X0} {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hv.1, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg]
  · have e : (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (dualMap φ) =
        φ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
      refine RingHom.ext fun z => ?_
      simp [dualMap]
    rw [← Category.assoc, spMap_comp', e, ← spMap_comp', Category.assoc, hv.2]
    let ψ : Over.mk (spMap φ ≫ x) ⟶ Over.mk x := Over.homMk (spMap φ) rfl
    exact congrArg (fun g => g.left) (MonObj.comp_one ψ : ψ ≫ (1 : Over.mk x ⟶ t.G) = 1)

end Generic

section Osc

variable [StarRing (𝓞 E)] {p : ℕ} [Fact p.Prime]

def nuPSup (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) (la : PointsOfFlagModel.abelian₂ p c)
    (cx : Lt1 Dw → ℕ) : EReal :=
  ⨆ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la.1 T.V io e) (y : IntFr Xo c T io) (_ : cls T io y),
    nuP p y cx

def nuPInf (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) (la : PointsOfFlagModel.abelian₂ p c)
    (cx : Lt1 Dw → ℕ) : EReal :=
  ⨅ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la.1 T.V io e) (y : IntFr Xo c T io) (_ : cls T io y),
    nuP p y cx

def eLoc {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (Z : Comp Xo c) (la : PointsOfFlagModel.abelian₂ p c)
    (cx : Lt1 Dw → ℕ) : EReal :=
  nuPSup (fun _ _ y => OnComp Z y ∧ y.IsAlg) la cx - nuPInf (fun _ _ y => OnComp Z y ∧ IsGen Y y) la cx

def ePLoc {O : PointsOfFlagModel.abelian₂ p c → Type} [∀ la, CommRing (O la)] {β : ∀ la, O la →+* c.F}
    (Y : ∀ la, Model Xo c (β la)) (cx : Lt1 Dw → ℕ) : EReal :=
  ⨆ (la : PointsOfFlagModel.abelian₂ p c) (Z : Comp Xo c), eLoc (Y la) Z la cx

variable {cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop} {la : PointsOfFlagModel.abelian₂ p c} {cx : Lt1 Dw → ℕ}

theorem nuPSup_le {r : EReal} (h : ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
    ∀ y : IntFr Xo c T io, cls T io y → nuP p y cx ≤ r) : nuPSup cls la cx ≤ r :=
  iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup₂_le (h T io e ho)

theorem le_nuPInf {r : EReal} (h : ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
    ∀ y : IntFr Xo c T io, cls T io y → r ≤ nuP p y cx) : r ≤ nuPInf cls la cx :=
  le_iInf fun T => le_iInf fun io => le_iInf fun e => le_iInf fun ho => le_iInf₂ (h T io e ho)

end Osc

example : ∑ j ∈ Finset.range 3, (if 0 < j + 1 then (fun i => if i = 0 then 5 else 2) j -
    (if j + 1 < 3 then (fun i => if i = 0 then 5 else 2) (j + 1) else 0) else 0) = 5 := by decide

example (n : ℕ) (f : Lt1 Dw) : gap Dw (fun _ => n) f = if rk f < Dw.mult f.1 then 0 else n := by
  unfold gap; split_ifs <;> simp

example {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) : polyP B 0 = 1 := by
  simp [polyP]

example (k : Type) [Field k] : TrdegGe (RatFunc k) 1 :=
  ⟨fun _ => RatFunc.X, algebraicIndependent_unique_type_iff.2 fun h => by
    let e := (algebraMap k (RatFunc k)).rangeRestrictFieldEquiv
    let g : (⊥ : Subfield (RatFunc k)) →+* k := e.symm.toRingHom.comp (Subfield.inclusion bot_le)
    refine RatFunc.transcendental_X (K := k) (h.ringHom_of_comp_eq g (RingHom.id _) g.injective ?_)
    ext z
    exact congrArg Subtype.val (e.apply_symm_apply (Subfield.inclusion bot_le z))⟩

end GlobalTheory.FactorDepth
