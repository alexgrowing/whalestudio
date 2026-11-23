import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameAfterExtIffAnd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

open NumberField IsDedekindDomain TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt GlobalTheory.FlagTan
open scoped ENNReal Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Tri

variable {K S : Type} [Field K] [Algebra c.F K] [CommRing S] [Algebra c.F S]

def Reframes (φ : K →ₐ[c.F] S) (y : FrPt Xo c K) (t : Ix Dw → Sˣ) (z : FrPt Xo c S) : Prop :=
  ∃ w, FrMap φ y w ∧ FrBor t w z

theorem Reframes.val_eq [IsLocalRing S] {φ : K →ₐ[c.F] S} {y : FrPt Xo c K} {t : Ix Dw → Sˣ} {z : FrPt Xo c S}
    (h : Reframes φ y t z) {e : Ix Dw → ℤ} {s : RulK Xo c K} (hs : s ∈ secK Xo c K e) :
    val φ z s = ((∏ i, t i ^ e i : Sˣ) : S) * φ (val (AlgHom.id c.F K) y s) := by
  obtain ⟨w, h₁, h₂⟩ := h
  rw [val_frBor hs φ h₂, val_frMap hs (φ := AlgHom.id c.F K) (fun _ => rfl) h₁]

theorem Reframes.evR_eq [IsLocalRing S] {φ : K →ₐ[c.F] S} {y : FrPt Xo c K} {t : Ix Dw → Sˣ} {z : FrPt Xo c S}
    (h : Reframes φ y t z) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    evR Xo c f z = ((∏ i, t i ^ e i : Sˣ) : S) * φ (evR Xo c f y) := by
  obtain ⟨w, h₁, h₂⟩ := h
  rw [evR_frBor hf h₂, evR_frMap hf.1 h₁]

theorem Reframes.liesOn {φ : K →ₐ[c.F] S} {y : FrPt Xo c K} {t : Ix Dw → Sˣ} {z : FrPt Xo c S}
    (h : Reframes φ y t z) {Z : Comp Xo c} (hy : LiesOn Z y) : LiesOn Z z := fun s => by
  obtain ⟨w, h₁, h₂⟩ := h
  have e : ptF z = CategoryTheory.CategoryStruct.comp (spMap φ.toRingHom) (ptF y) := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · simp only [ptF, CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst]
      exact h₂.1.trans h₁.1
    · simp only [ptF, CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd]
      rw [← AlgebraicGeometry.Spec.map_comp]
      exact congrArg spMap φ.comp_algebraMap.symm
  rw [e, AlgebraicGeometry.Scheme.Hom.comp_apply]
  exact hy _

end Tri

section Fin

variable {K : Type} [Field K] [NumberField K] [Algebra c.F K]

omit [Algebra c.F K] in

theorem nrmOf_nonneg (la : HeightOneSpectrum (𝓞 K)) (w : EReal) : 0 ≤ nrmOf la w := by
  simp only [nrmOf]
  split_ifs
  exacts [le_rfl, by positivity]

omit [Algebra c.F K] in

theorem nrmOf_anti (la : HeightOneSpectrum (𝓞 K)) {w w' : EReal} (hw : w ≠ ⊥) (h : w ≤ w') :
    nrmOf la w' ≤ nrmOf la w := by
  by_cases ht : w' = ⊤
  · rw [ht, nrmOf, if_pos rfl]; exact nrmOf_nonneg _ _
  rw [nrmOf, nrmOf, if_neg ht, if_neg (ne_top_of_le_ne_top ht h)]
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_absNorm_real la).le (neg_le_neg (EReal.toReal_le_toReal h hw ht))

structure FinFr (y : FrPt Xo c K) (v : FinitePlace K) : Type 1 where

  T : CDVR

  io : c.F →+* T.Fr

  φ : CoefHom c io K

  e : ℕ

  lies : letI := io.toAlgebra; OverLa v.maximalIdeal T.V φ.toRingHom e

  fin : T.FinRes

  pt : IntFr Xo c T io

  t : Ix Dw → T.Frˣ

  tri : letI := io.toAlgebra; Reframes φ y t pt.1

instance FinFr.nonempty (y : FrPt Xo c K) (v : FinitePlace K) : Nonempty (FinFr y v) := by
  have hE : IntFrExt Xo c := (Nat.eq_zero_or_pos (Dw.p + Dw.q)).elim
    (GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero E H Dw l Xo c) (GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c)
  obtain ⟨T₀, j, ho, hf, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K v.maximalIdeal
  letI := (j.comp (algebraMap c.F K)).toAlgebra
  obtain ⟨w₀, h₀⟩ := exists_frMap (⟨j, fun _ => rfl⟩ : K →ₐ[c.F] T₀.Fr) y
  obtain ⟨T, i, r, hr, hi, hf', y₁, hx⟩ := hE T₀ _ hf w₀.x w₀.x_over
  letI := (i.comp (j.comp (algebraMap c.F K))).toAlgebra
  let φ : K →ₐ[c.F] T.Fr := ⟨i.comp j, fun _ => rfl⟩
  obtain ⟨w, hw⟩ := exists_frMap (⟨i, fun _ => rfl⟩ : T₀.Fr →ₐ[c.F] T.Fr) w₀
  obtain ⟨t, z, hz⟩ := GlobalTheory.AlgLawsCompare.reFrame T _ y₁ w (hw.1.trans hx.symm)
  exact ⟨⟨T, _, φ, _, ho.bc i hr hi, hf', z, t, w, frMap_comp h₀ hw fun _ => rfl, hz⟩⟩

namespace FinFr

variable {y : FrPt Xo c K} {v : FinitePlace K} (F : FinFr y v)

instance algebra : Algebra c.F F.T.Fr := F.io.toAlgebra

def abs : AbsoluteValue F.T.Fr ℝ where
  toFun a := nrmOf v.maximalIdeal (nval F.T.V F.e a)
  map_mul' a b := by
    have h1 := one_lt_absNorm_real v.maximalIdeal
    by_cases ha : a = 0
    · simp [ha, nval_zero, nrmOf]
    by_cases hb : b = 0
    · simp [hb, nval_zero, nrmOf]
    rw [nval_mul, nval_of_ne ha, nval_of_ne hb, ← EReal.coe_add]
    simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe]
    rw [neg_add, Real.rpow_add (by linarith)]
  nonneg' a := nrmOf_nonneg _ _
  eq_zero' a := by
    have h1 := one_lt_absNorm_real v.maximalIdeal
    by_cases ha : a = 0
    · simp [ha, nval_zero, nrmOf]
    rw [nval_of_ne ha]
    simp only [nrmOf, EReal.coe_ne_top, if_false, ha, iff_false]
    exact (Real.rpow_pos_of_pos (by linarith) _).ne'
  add_le' a b := by
    rcases min_le_iff.1 (nval_add (V := F.T.V) F.e a b) with h | h
    · exact (nrmOf_anti _ (nval_ne_bot _ _) h).trans (le_add_of_nonneg_right (nrmOf_nonneg _ _))
    · exact (nrmOf_anti _ (nval_ne_bot _ _) h).trans (le_add_of_nonneg_left (nrmOf_nonneg _ _))

theorem abs_apply (a : F.T.Fr) : F.abs a = nrmOf v.maximalIdeal (nval F.T.V F.e a) := rfl

theorem abs_φ (a : K) : F.abs (F.φ a) = v a := by
  by_cases ha : a = 0
  · simp [ha]
  have h := nrmOf_smul v.maximalIdeal ha (nval_ne_bot (V := F.T.V) F.e (1 : F.T.Fr))
  rw [← nval_smul F.lies ha, mul_one, FinitePlace.mk_maximalIdeal, ← abs_apply, ← abs_apply, map_one, mul_one] at h
  exact h

theorem abs_add_le_max (a b : F.T.Fr) : F.abs (a + b) ≤ max (F.abs a) (F.abs b) :=
  le_max_iff.2 ((min_le_iff.1 (nval_add (V := F.T.V) F.e a b)).imp (nrmOf_anti _ (nval_ne_bot _ _))
    (nrmOf_anti _ (nval_ne_bot _ _)))

theorem abs_φ_le_one (a : 𝓞 K) : F.abs (F.φ a) ≤ 1 := by
  rw [F.abs_φ, ← v.norm_embedding_eq]
  exact FinitePlace.norm_le_one _ _ _

theorem ofReal_abs (a : F.T.Fr) :
    ENNReal.ofReal (F.abs a) = normOfOrd (Ideal.absNorm v.maximalIdeal.asIdeal) (nval F.T.V F.e a) := by
  have h1 := one_lt_absNorm_real v.maximalIdeal
  by_cases ha : a = 0
  · rw [ha, map_zero, nval_zero, normOfOrd, EReal.top_mul_coe_of_pos (Real.log_pos h1)]
    simp
  rw [abs_apply, nval_of_ne ha, normOfOrd, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
  simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe]
  rw [Real.rpow_def_of_pos (by linarith)]
  congr 2
  ring

def nrm (f : Rul Xo c) : ℝ := F.abs (evI F.pt f)

def fac (e : Ix Dw → ℤ) : ℝ := F.abs ((∏ i, F.t i ^ e i : F.T.Frˣ) : F.T.Fr)

theorem nrm_nonneg (f : Rul Xo c) : 0 ≤ F.nrm f := F.abs.nonneg _

theorem nrm_mul (f g : Rul Xo c) : F.nrm (f * g) = F.nrm f * F.nrm g := by rw [nrm, evI_mul, map_mul]; rfl

theorem fac_pos (e : Ix Dw → ℤ) : 0 < F.fac e := F.abs.pos (Units.ne_zero _)

theorem fac_add (e e' : Ix Dw → ℤ) : F.fac (e + e') = F.fac e * F.fac e' := by
  simp only [fac, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul, map_mul]

theorem fac_zero : F.fac 0 = 1 := by simp [fac]

theorem nrm_eq {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) : F.nrm f = F.fac e * v (evR Xo c f y) := by
  rw [← F.abs_φ, fac, ← map_mul, ← F.tri.evR_eq hf]
  rfl

theorem exists_mem_valSet : ∃ (la : HeightOneSpectrum (𝓞 c.F)) (e' : ℕ), OverLa la F.T.V F.io e' ∧
    (fun f => nval F.T.V e' (evI F.pt f)) ∈ valSet Xo c (algCls Xo c) la := by
  let w := v.maximalIdeal
  have : w.asIdeal.LiesOver (w.under (𝓞 c.F)).asIdeal := ⟨rfl⟩
  have ho : OverLa (w.under (𝓞 c.F)) F.T.V F.io (F.e * (w.under (𝓞 c.F)).asIdeal.ramificationIdx' w.asIdeal) := by
    refine ⟨Nat.mul_pos F.lies.1 (Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 c.F)).ne_bot)), fun a => ?_⟩
    rw [show F.io a = F.φ.toRingHom (algebraMap c.F K a) from (F.φ.commutes a).symm, F.lies.2, vLa, vLa,
      ← HeightOneSpectrum.valuation_liesOver K (w.under (𝓞 c.F)) w a, WithZero.log_pow]
    simp [mul_assoc]
  exact ⟨_, _, ho, PtV.mk _ ho F.pt F.fin () trivial, rfl⟩

theorem nrm_le_one {C : Submodule c.F (Rul Xo c)} {f : C} (hf : f ∈ supLat C) : F.nrm f ≤ 1 := by
  obtain ⟨la, e', ho, h⟩ := F.exists_mem_valSet
  have h0 : 0 ≤ nval F.T.V e' (evI F.pt f) := hf la _ h
  refine (nrmOf_le_one_iff _ (nval_ne_bot _ _)).2 ?_
  by_cases hz : evI F.pt f = 0
  · rw [hz, nval_zero]; exact le_top
  rw [nval_of_ne hz, EReal.coe_nonneg] at h0 ⊢
  have := (le_div_iff₀ (by exact_mod_cast ho.1)).1 h0
  exact div_nonneg (by simpa using this) (Nat.cast_nonneg _)

def latMax (C : Submodule c.F (Rul Xo c)) : ℝ := ⨆ w : supLat C, F.nrm w.1

theorem bddAbove_nrm (C : Submodule c.F (Rul Xo c)) : BddAbove (Set.range fun w : supLat C => F.nrm w.1) :=
  ⟨1, by rintro _ ⟨w, rfl⟩; exact F.nrm_le_one w.2⟩

theorem nrm_le_latMax {C : Submodule c.F (Rul Xo c)} {f : C} (hf : f ∈ supLat C) : F.nrm f ≤ F.latMax C :=
  le_ciSup (F.bddAbove_nrm C) ⟨f, hf⟩

theorem latMax_le_iff {C : Submodule c.F (Rul Xo c)} {B : ℝ} : F.latMax C ≤ B ↔ ∀ f ∈ supLat C, F.nrm f.1 ≤ B :=
  (ciSup_le_iff (F.bddAbove_nrm C)).trans Subtype.forall

theorem latMax_mem (C : Submodule c.F (Rul Xo c)) : 0 ≤ F.latMax C ∧ F.latMax C ≤ 1 :=
  ⟨(F.nrm_nonneg _).trans (F.nrm_le_latMax (zero_mem _)), F.latMax_le_iff.2 fun _ => F.nrm_le_one⟩

theorem latMax_le_of_span {C : Submodule c.F (Rul Xo c)} {κ : Type} {g : κ → C}
    (hg : supLat C ≤ Submodule.span (𝓞 c.F) (Set.range g)) {B : ℝ} (hB : 0 ≤ B) (h : ∀ k, F.nrm (g k) ≤ B) :
    F.latMax C ≤ B := F.latMax_le_iff.2 fun f hf => by
  replace hf := hg hf
  induction hf using Submodule.span_induction with
  | mem _ e => obtain ⟨k, rfl⟩ := e; exact h k
  | zero => exact (congrArg F.abs ((isEval_evI F.pt).zero ())).le.trans (by simpa using hB)
  | add a b _ _ ha hb => exact (congrArg F.abs (evI_add F.pt _ _)).le.trans ((F.abs_add_le_max _ _).trans (max_le ha hb))
  | smul a f _ hf =>
    refine (congrArg F.abs (evI_smul F.pt (a : c.F) f.1)).le.trans ?_
    rw [map_mul, show F.io a = F.φ (algebraMap (𝓞 c.F) (𝓞 K) a) from (F.φ.commutes _).symm]
    exact (mul_le_of_le_one_left (F.abs.nonneg _) (F.abs_φ_le_one _)).trans hf

variable {ι : Type} [Fintype ι]

def wedgeNrm (s : ι → RulK Xo c K) : ℝ≥0∞ :=
  normOfOrd (Ideal.absNorm v.maximalIdeal.asIdeal) (wedgeOrd (psiSet H) F.e F.φ F.pt s)

theorem wedgeNrm_spec {s : ι → RulK Xo c K} (h : F.wedgeNrm s ≠ ⊤) :
    (∃ o d, IsWedgeVal (psiSet H) o F.φ F.pt.1 s d) ∧
      ∀ o d, IsWedgeVal (psiSet H) o F.φ F.pt.1 s d → F.wedgeNrm s = ENNReal.ofReal (F.abs d) := by
  have hb : wedgeOrd (psiSet H) F.e F.φ F.pt s ≠ ⊥ := fun e => h (by
    rw [wedgeNrm, e, normOfOrd, EReal.bot_mul_coe_of_pos (Real.log_pos (one_lt_absNorm_real _))]
    simp)
  obtain ⟨w, ⟨o, d, hd, -⟩, -⟩ := wedgeOrd_ne_bot_iff.1 hb
  exact ⟨⟨o, d, hd⟩, fun o d hd => by rw [wedgeNrm, wedgeOrd_eq hb ⟨o, d, hd, rfl⟩, ofReal_abs]⟩

theorem wedgeNrm_eq (h : KSIso (psiSet H) F.pt.1) {e : Ix Dw → ℤ} {s : ι → RulK Xo c K}
    (hs : ∀ i, s i ∈ secK Xo c K e) {o : ι ≃ TIx Dw (psiSet H)} {d : F.T.Fr}
    (hd : IsWedgeVal (psiSet H) o F.φ F.pt.1 s d) : F.wedgeNrm s = ENNReal.ofReal (F.abs d) := by
  rw [wedgeNrm, h.wedgeOrd_eq F.e hs hd, ofReal_abs]

example (hq : Dw.q = 0) {e : Ix Dw → ℤ} {s : Fin (dimFlag Dw) → RulK Xo c K} (hs : ∀ i, s i ∈ secK Xo c K e)
    (h0 : ∀ i, val (AlgHom.id c.F K) y (s i) = 0) : F.wedgeNrm s ≠ ⊤ := by
  haveI := isEmpty_HIx (Dw := Dw) (psiSet H) (Or.inr hq)
  have h := existsUnique_isWedgeVal_of_isEmpty (Φ := psiSet H) (tanOrd Dw) F.φ (y := F.pt.1) (s := s) fun i => by
    rw [F.tri.val_eq (hs i), h0, map_zero, mul_zero]
  obtain ⟨d, hd⟩ := h.exists
  rw [wedgeNrm, wedgeOrd_eq_of_unique F.e h hd, ← ofReal_abs]
  exact ENNReal.ofReal_ne_top

end FinFr

end Fin

section Primes

variable {K : Type} [Field K] [NumberField K]

def primeWt (S : Finset ℕ) (b : ℕ → ℝ) (v : FinitePlace K) : ℝ := ∑ p ∈ S, b p * -Real.log (v (p : K))

theorem finite_support_log {a : K} (ha : a ≠ 0) : (Function.support fun v : FinitePlace K => Real.log (v a)).Finite :=
  (FinitePlace.hasFiniteMulSupport ha).subset fun v hv h => hv (by simp only at h ⊢; rw [h, Real.log_one])

theorem finsum_log_natCast {p : ℕ} (hp : p ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (v (p : K)) = -(Module.finrank ℚ K * Real.log p) := by
  have h0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [← Real.log_finprod fun v : FinitePlace K => FinitePlace.pos_iff.2 h0, FinitePlace.prod_eq_inv_abs_norm h0,
    show (p : K) = algebraMap ℚ K p from (map_natCast _ p).symm, Algebra.norm_algebraMap]
  simp

theorem finite_support_primeWt {S : Finset ℕ} (hS : 0 ∉ S) (b : ℕ → ℝ) :
    (Function.support (primeWt (K := K) S b)).Finite := by
  refine (S.finite_toSet.biUnion fun p hp => finite_support_log (K := K) (a := p)
    (Nat.cast_ne_zero.2 fun e => hS (e ▸ hp))).subset fun v hv => ?_
  obtain ⟨p, hp, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_biUnion hp fun e => h (by simp only at e; rw [e, neg_zero, mul_zero])

theorem finsum_primeWt {S : Finset ℕ} (hS : 0 ∉ S) (b : ℕ → ℝ) :
    (∑ᶠ v, primeWt (K := K) S b v) / (Module.finrank ℚ K : ℝ) = ∑ p ∈ S, b p * Real.log p := by
  have h0 : ∀ p ∈ S, p ≠ 0 := fun p hp e => hS (e ▸ hp)
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold primeWt
  rw [finsum_sum_comm S (fun v p => b p * -Real.log (v (p : K))) fun p hp => (finite_support_log (K := K) (a := p) (Nat.cast_ne_zero.2 (h0 p hp))).subset
    fun v hv e => hv (by simp only at e ⊢; rw [e, neg_zero, mul_zero]), Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← mul_finsum, finsum_neg_distrib, finsum_log_natCast (h0 p hp)]
  field_simp

theorem exp_primeWt {S : Finset ℕ} (b : ℕ → ℝ) (v : FinitePlace K) {p : ℕ} (hp : p ∈ S) (h0 : p ≠ 0)
    (h : ∀ q ∈ S, q ≠ p → v (q : K) = 1) : Real.exp (primeWt S b v) = v (p : K) ^ (-b p) := by
  rw [primeWt, Finset.sum_eq_single_of_mem p hp fun q hq e => by simp [h q hq e],
    Real.rpow_def_of_pos (FinitePlace.pos_iff.2 (Nat.cast_ne_zero.2 h0))]
  congr 1
  ring

theorem primeWt_eq_zero {S : Finset ℕ} (b : ℕ → ℝ) (v : FinitePlace K) (h : ∀ q ∈ S, v (q : K) = 1) :
    primeWt S b v = 0 := Finset.sum_eq_zero fun q hq => by simp [h q hq]

example : (∑ᶠ v, primeWt (K := K) {2} (fun _ => 3) v) / (Module.finrank ℚ K : ℝ) = 3 * Real.log 2 := by
  rw [finsum_primeWt (by simp)]; simp

variable [Algebra c.F K] {y : FrPt Xo c K} {v : FinitePlace K} (F : FinFr y v)

namespace FinFr

theorem abs_eq_rpow {p : ℕ} (hp : p ≠ 0) (h : (p : F.T.V) ∈ IsLocalRing.maximalIdeal F.T.V) {a : F.T.Fr} {w : ℝ}
    (hw : nval F.T.V (ramIdx F.T p) a = w) : F.abs a = v (p : K) ^ w ∧ v (p : K) < 1 := by
  have h1 := one_lt_absNorm_real v.maximalIdeal
  obtain ⟨hr, hv⟩ := ramIdx_spec hp h
  have hr' : (0 : ℝ) < ramIdx F.T p := by exact_mod_cast hr
  have he : (0 : ℝ) < F.e := by exact_mod_cast F.lies.1
  have ha : a ≠ 0 := fun e => by rw [e, nval_zero] at hw; exact EReal.top_ne_coe _ hw
  have h0 : (p : F.T.Fr) ≠ 0 := fun e => by rw [e, nval_zero] at hv; exact EReal.top_ne_coe 1 hv
  rw [nval_of_ne h0] at hv
  rw [nval_of_ne ha] at hw
  replace hv : (vV F.T.V (p : F.T.Fr) : ℝ) = ramIdx F.T p := (div_eq_one_iff_eq hr'.ne').1 (EReal.coe_injective hv)
  rw [← F.abs_φ, map_natCast, abs_apply, abs_apply, nval_of_ne ha, nval_of_ne h0, ← EReal.coe_injective hw, hv]
  simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe]
  refine ⟨?_, Real.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.2 (div_pos hr' he))⟩
  rw [← Real.rpow_mul (by linarith)]
  congr 1
  field_simp

theorem exists_prime : ∃ p : ℕ, p.Prime ∧ (p : F.T.V) ∈ IsLocalRing.maximalIdeal F.T.V ∧
    ∀ q : ℕ, q.Prime → q ≠ p → v (q : K) = 1 := by
  haveI : Finite (IsLocalRing.ResidueField F.T.V) := F.fin
  obtain ⟨p, hc⟩ := CharP.exists (IsLocalRing.ResidueField F.T.V)
  have hp : p.Prime := CharP.char_is_prime (IsLocalRing.ResidueField F.T.V) p
  refine ⟨p, hp, (IsLocalRing.residue_eq_zero_iff _).1 (by simp), fun q hq e => ?_⟩
  have hu : IsUnit (q : F.T.V) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by
    rw [map_natCast, Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField F.T.V) p]
    exact fun h => e ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm)
  have h1 := GlobalTheory.PlaceCompletion.valV_algebraMap_of_isUnit (K' := F.T.Fr) hu
  rw [map_natCast] at h1
  have h0 : (q : F.T.Fr) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  rw [← F.abs_φ, map_natCast, abs_apply, nval_of_ne h0, vV, h1]
  simp [nrmOf]

theorem wedgeNrm_le_of_wedgeNorm_le {ι : Type} [Fintype ι] {s : ι → RulK Xo c K} {p : ℕ} (hp : 1 < p)
    (h : (p : F.T.V) ∈ IsLocalRing.maximalIdeal F.T.V) {b : ℝ}
    (hb : wedgeNorm (psiSet H) p F.φ F.pt s ≤ ENNReal.ofReal ((p : ℝ) ^ b)) :
    F.wedgeNrm s ≤ ENNReal.ofReal (v (p : K) ^ (-b)) := by
  have hp0 : p ≠ 0 := by omega
  rw [wedgeNorm_le_iff hp, wedgeOrd_vp] at hb
  have hne := ((EReal.bot_lt_coe _).trans_le hb).ne'
  obtain ⟨w, ⟨o, d, hd, -⟩, -⟩ := wedgeOrd_ne_bot_iff.1 hne
  have key : ∀ o d, IsWedgeVal (psiSet H) o F.φ F.pt.1 s d → _ = nval F.T.V (ramIdx F.T p) d :=
    fun o d hd => wedgeOrd_eq hne ⟨o, d, hd, rfl⟩
  have hr : ((ramIdx F.T p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ramIdx_spec hp0 h).1.ne'
  have hu : ∃! w, IsWedgeOrd (psiSet H) F.e F.φ F.pt s w := ⟨_, ⟨o, d, hd, rfl⟩, by
    rintro _ ⟨o', d', hd', rfl⟩
    have e := (key o' d' hd').symm.trans (key o d hd)
    unfold nval at e ⊢
    split_ifs at e ⊢ with h₁ h₂ h₂
    · rfl
    · exact absurd e (EReal.top_ne_coe _)
    · exact absurd e (EReal.coe_ne_top _)
    · rw [(div_left_inj' hr).1 (EReal.coe_injective e)]⟩
  rw [wedgeNrm, wedgeOrd_eq (wedgeOrd_ne_bot_iff.2 hu) ⟨o, d, hd, rfl⟩, ← ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases h0 : d = 0
  · rw [h0, map_zero]; positivity
  rw [key o d hd, nval_of_ne h0] at hb
  obtain ⟨e₁, e₂⟩ := F.abs_eq_rpow hp0 h (nval_of_ne h0)
  rw [e₁]
  exact Real.rpow_le_rpow_of_exponent_ge (FinitePlace.pos_iff.2 (Nat.cast_ne_zero.2 hp0)) e₂.le
    (EReal.coe_le_coe_iff.1 hb)

end FinFr

end Primes

section Inf

variable {K : Type} [Field K] [Algebra c.F K] {r : ℕ}

variable (c) in

abbrev baseEmb (τ : K →+* ℂ) : c.F →+* ℂ := goodOf c (τ.comp (algebraMap c.F K))

variable (c) in

def goodHom (τ : K →+* ℂ) : K →ₐ[c.F] CAt (baseEmb c τ) :=
  if h : GoodEmb c (τ.comp (algebraMap c.F K)) then
    ⟨τ, fun a => (DFunLike.congr_fun (if_pos h : baseEmb c τ = _) a).symm⟩
  else ⟨(starRingEnd ℂ).comp τ, fun a => (DFunLike.congr_fun (if_neg h : baseEmb c τ = _) a).symm⟩

theorem norm_goodHom (τ : K →+* ℂ) (a : K) : ‖toC (goodHom c τ a)‖ = ‖τ a‖ := by
  unfold goodHom
  split_ifs
  · rfl
  · exact Complex.norm_conj _

structure InfFr (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (y : FrPt Xo c K) (τ : K →+* ℂ) : Type where

  k : (U (baseEmb c τ)).Comp

  z : ((U (baseEmb c τ)).X k).dom

  t : Ix Dw → (CAt (baseEmb c τ))ˣ

  tri : Reframes (goodHom c τ) y t ((U (baseEmb c τ)).un k z)

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {y : FrPt Xo c K} {τ : K →+* ℂ}

theorem InfFr.nonempty (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (y : FrPt Xo c K) (τ : K →+* ℂ) :
    Nonempty (InfFr U y τ) := by
  obtain ⟨w, hw⟩ := exists_frMap (goodHom c τ) y
  obtain ⟨k, z, t, h⟩ := (hU _ (goodEmb_goodOf c _)).2.2.1 w
  exact ⟨⟨k, z, t⁻¹, w, hw, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ h⟩⟩

namespace InfFr

variable (F : InfFr U y τ) (x : ℝ)

abbrev pt : Σ k, FD.Frame ((U (baseEmb c τ)).X k).Ψ r := ⟨F.k, F.z.1⟩

theorem mem_framesOn {Z : Comp Xo c} (hy : LiesOn Z y) : F.pt ∈ framesOn (U (baseEmb c τ)) Z :=
  ⟨F.z.2, F.tri.liesOn hy⟩

def nrm (G : WTZ E) (f : Rul Xo c) : ℝ := homN (U (baseEmb c τ)) x G f F.pt

def fac (G : WTZ E) : ℝ :=
  lieFacZ Dw x G * ((U (baseEmb c τ)).X F.k).nfac (modelWt (U (baseEmb c τ)) G F.k) F.z.1 *
    ‖toC ((∏ i, F.t i ^ exZ Dw G i : (CAt (baseEmb c τ))ˣ) : CAt (baseEmb c τ))‖

theorem nrm_nonneg (G : WTZ E) (f : Rul Xo c) : 0 ≤ F.nrm x G f := homN_nonneg _ _ _ _ _

theorem fac_pos (G : WTZ E) : 0 < F.fac x G :=
  mul_pos (mul_pos (lieFacZ_pos _ _) (FD.BoundedSectionAlgebra.nfac_pos _ F.z.2 _))
    (norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) _))

theorem fac_add {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) : F.fac x (G + G') = F.fac x G * F.fac x G' := by
  have e : ∀ a b : CAt (baseEmb c τ), ‖toC (a * b)‖ = ‖toC a‖ * ‖toC b‖ := fun a b => norm_mul (toC a) (toC b)
  simp only [fac, lieFacZ_add, modelWt_add _ hG hG', FD.BoundedSectionAlgebra.nfac_add _ F.z.2, exZ_add, zpow_add,
    Finset.prod_mul_distrib, Units.val_mul, e]
  ring

theorem nrm_eq {G : WTZ E} {f : Rul Xo c} (hf : f ∈ secZ Xo c (exZ Dw G)) :
    F.nrm x G f = F.fac x G * ‖τ (evR Xo c f y)‖ := by
  haveI : IsLocalRing (CAt (baseEmb c τ)) := inferInstanceAs (IsLocalRing ℂ)
  have e : rdU (U (baseEmb c τ)) f F.k F.z.1 = toC (evR Xo c f ((U (baseEmb c τ)).un F.k F.z)) := dif_pos F.z.2
  have e' : ∀ a b : CAt (baseEmb c τ), ‖toC (a * b)‖ = ‖toC a‖ * ‖toC b‖ := fun a b => norm_mul (toC a) (toC b)
  show _ * (‖rdU (U (baseEmb c τ)) f F.k F.z.1‖ * FD.Data.nfac _ _ _) = _
  rw [e, F.tri.evR_eq hf, e', norm_goodHom, fac]
  ring

end InfFr

end Inf

section Berg

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : Formalism.BasicNotions.D7} (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (Z : Comp Xo c)

def bergCusp (G : WTZ E) (σ : c.F →+* ℂ) (z : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) : ℝ≥0∞ :=
  ⨆ f ∈ cuspOn U Z G, ENNReal.ofReal (homN (U (goodOf c σ)) x G f z) ^ 2 / ENNReal.ofReal (petOn U x V dict Z G σ f) ^ 2

variable {U x V dict Z}

theorem bergCusp_le_iff {G : WTZ E} {σ : c.F →+* ℂ} {z : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r} {B : ℝ}
    (hB : 0 ≤ B) : bergCusp U x V dict Z G σ z ≤ ENNReal.ofReal B ↔
      ∀ f ∈ cuspOn U Z G, homN (U (goodOf c σ)) x G f z ^ 2 ≤ B * petOn U x V dict Z G σ f ^ 2 := by
  simp only [bergCusp, iSup_le_iff]
  refine forall₂_congr fun f _ => ?_
  have hp : 0 ≤ petOn U x V dict Z G σ f := petAt_nonneg _ _ _ _ _ _ _
  rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)),
    ← ENNReal.ofReal_pow (homN_nonneg _ _ _ _ _), ← ENNReal.ofReal_pow hp, ← ENNReal.ofReal_mul hB,
    ENNReal.ofReal_le_ofReal_iff (by positivity)]

theorem bergCusp_le_bergOn {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (z : FPt (U (goodOf c σ)).X) : bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ ≤
      bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z := by
  by_cases h : bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z = ⊤
  · exact h ▸ le_top
  rw [← ENNReal.ofReal_toReal h, bergCusp_le_iff ENNReal.toReal_nonneg]
  exact fun f hf => homN_sq_le _ x _ _ _ (muPart_univ_le _ _ _) hd z ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal h).ge ((mem_cuspW.1 hf.1).2 _ (goodEmb_goodOf c σ))

end Berg

section Statements

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : Formalism.BasicNotions.D7} (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (P : WtPar Dw)

def latExt (K : Type) [Field K] [Algebra c.F K] (la : AllWt.Weight Dw) : Submodule (𝓞 K) (RulK Xo c K) :=
  Submodule.span (𝓞 K) (Set.range fun w : latOn U Z (wtOf Dw la 0) => (1 : K) ⊗ₜ[c.F] (w.1.1 : Rul Xo c))

variable {U Z} in

theorem latExt_le_secK {K : Type} [Field K] [Algebra c.F K] {la : AllWt.Weight Dw} {s : RulK Xo c K}
    (hs : s ∈ latExt U Z K la) : s ∈ secK Xo c K (exOf Dw la 0) :=
  (Submodule.span_le (p := (secK Xo c K (exOf Dw la 0)).restrictScalars (𝓞 K))).2
    (by rintro _ ⟨w, rfl⟩; exact tmul_mem_secK (cusp_le_secZ Z U la w.1.2) 1) hs

variable {U Z} in

theorem FinFr.abs_val_le_one {K : Type} [Field K] [NumberField K] [Algebra c.F K] {y : FrPt Xo c K} {v : FinitePlace K}
    (F : FinFr y v) {la : AllWt.Weight Dw} {s : RulK Xo c K} (hs : s ∈ latExt U Z K la) :
    F.abs (val F.φ F.pt.1 s) ≤ 1 := by
  have key : ∀ a : F.T.Fr, F.abs a ≤ 1 ↔ 0 ≤ nval F.T.V F.e a := fun a => nrmOf_le_one_iff _ (nval_ne_bot _ _)
  induction hs using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨w, rfl⟩ := h
    rw [val_tmul, map_one, one_mul]
    exact F.nrm_le_one w.2
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, key]
    exact (le_min ((key _).1 ha) ((key _).1 hb)).trans (nval_add _ _ _)
  | smul a s _ hs =>
    rw [show a • s = (a : K) • s from (algebraMap_smul K a s).symm, val_smul, map_mul]
    exact mul_le_one₀ (F.abs_φ_le_one a) (F.abs.nonneg _) hs

def WtPar.tauWt : AllWt.Weight Dw := (dimFlag Dw + 3) • P.u₁ - P.uc

theorem WtPar.kap_add_tauWt :
    (kap Dw + dimFlag Dw • P.u₁) + P.u₂ + P.tauWt = (dimFlag Dw + 3) • P.u₁ := by
  rw [WtPar.tauWt, WtPar.uc]; abel

section At

variable {K : Type} [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K)

def JacFinAt (X : ℝ) : Prop :=
  ∀ s : Fin (dimFlag Dw) → RulK Xo c K, (∀ i, s i ∈ latExt U Z K P.u₁) → (∀ i, val (AlgHom.id c.F K) y (s i) = 0) →
    ∃ t : FinitePlace K → ℝ, (Function.support t).Finite ∧
      (∀ v (F : FinFr y v), F.wedgeNrm s ≤ ENNReal.ofReal (Real.exp (t v))) ∧
      (∑ᶠ v, t v) / (Module.finrank ℚ K : ℝ) ≤ X

def TauBd (m : ℕ) (τ : Rul Xo c) (t : FinitePlace K → ℝ) (A : (K →+* ℂ) → ℝ) : Prop :=
  (∀ v (F : FinFr y v), F.nrm τ ≤ Real.exp (t v) * F.latMax (Cusp Z U P.u₁) ^ (m * (dimFlag Dw + 3))) ∧
    ∀ ρ : K →+* ℂ, Nonempty (InfFr U y ρ) ∧ ∀ F : InfFr U y ρ,
      bergCusp U x V dict Z (wtOf Dw P.u₁ 0) (ρ.comp (algebraMap c.F K)) F.pt ≠ ⊤ ∧
      F.nrm x (wtOf Dw (m • P.tauWt) 0) τ ≤ A ρ *
        √(bergCusp U x V dict Z (wtOf Dw P.u₁ 0) (ρ.comp (algebraMap c.F K)) F.pt).toReal ^ (m * (dimFlag Dw + 3))

def TauPtAt (X : ℝ) : Prop :=
  ∃ (m : ℕ) (τ : Rul Xo c) (t : FinitePlace K → ℝ) (A : (K →+* ℂ) → ℝ), 1 ≤ m ∧
    τ ∈ secZ Xo c (exOf Dw (m • P.tauWt) 0) ∧ evR Xo c τ y ≠ 0 ∧ (Function.support t).Finite ∧ (∀ ρ, 0 < A ρ) ∧
    TauBd U x V dict Z P y m τ t A ∧ (∑ᶠ v, t v) / (Module.finrank ℚ K : ℝ) + meanLog K A ≤ m * X

variable {U x V dict Z P y}

theorem JacFinAt.mono {X X' : ℝ} (h : JacFinAt U Z P y X) (e : X ≤ X') : JacFinAt U Z P y X' :=
  fun s hs h0 => (h s hs h0).imp fun _ k => ⟨k.1, k.2.1, k.2.2.trans e⟩

theorem TauPtAt.mono {X X' : ℝ} (h : TauPtAt U x V dict Z P y X) (e : X ≤ X') : TauPtAt U x V dict Z P y X' := by
  obtain ⟨m, τ, t, A, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  exact ⟨m, τ, t, A, h₁, h₂, h₃, h₄, h₅, h₆, h₇.trans (mul_le_mul_of_nonneg_left e m.cast_nonneg)⟩

theorem JacFinAt.of_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (b : ℕ → ℝ)
    (h : ∀ s : Fin (dimFlag Dw) → RulK Xo c K, (∀ i, s i ∈ latExt U Z K P.u₁) →
      (∀ i, val (AlgHom.id c.F K) y (s i) = 0) → ∀ v (F : FinFr y v) (p : ℕ), p.Prime →
      (p : F.T.V) ∈ IsLocalRing.maximalIdeal F.T.V →
      wedgeNorm (psiSet H) p F.φ F.pt s ≤ ENNReal.ofReal ((p : ℝ) ^ (if p ∈ S then b p else 0))) :
    JacFinAt U Z P y (∑ p ∈ S, b p * Real.log p) := fun s hs h0 => by
  have hS0 : 0 ∉ S := fun e => Nat.not_prime_zero (hS 0 e)
  refine ⟨primeWt S b, finite_support_primeWt hS0 b, fun v F => ?_, (finsum_primeWt hS0 b).le⟩
  obtain ⟨p, hp, hm, hq⟩ := F.exists_prime
  refine (F.wedgeNrm_le_of_wedgeNorm_le hp.one_lt hm (h s hs h0 v F p hp hm)).trans (le_of_eq (congrArg _ ?_))
  split_ifs with hpS
  · exact (exp_primeWt b v hpS hp.ne_zero fun q h e => hq q (hS q h) e).symm
  · rw [primeWt_eq_zero b v fun q h => hq q (hS q h) fun e => hpS (e ▸ h)]
    simp

theorem TauPtAt.latMax_pos {X : ℝ} (h : TauPtAt U x V dict Z P y X) {v : FinitePlace K} (F : FinFr y v) :
    0 < F.latMax (Cusp Z U P.u₁) := by
  obtain ⟨m, τ, t, A, h₁, h₂, h₃, -, -, h₆, -⟩ := h
  refine (F.latMax_mem _).1.lt_of_ne fun e => ?_
  have := h₆.1 v F
  rw [← e, zero_pow (by positivity), mul_zero, F.nrm_eq h₂] at this
  exact this.not_gt (mul_pos (F.fac_pos _) (FinitePlace.pos_iff.2 h₃))

example (h : ∀ f ∈ Cusp Z U P.u₁, evR Xo c f y = 0) (v : FinitePlace K) (X : ℝ) : ¬ TauPtAt U x V dict Z P y X :=
  fun k => by
    obtain ⟨F⟩ := FinFr.nonempty y v
    exact (k.latMax_pos F).not_ge (F.latMax_le_iff.2 fun f _ => by
      rw [F.nrm_eq (cusp_le_secZ Z U _ f.2), h _ f.2]; simp)

end At

def JacFin (X : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → JacFinAt U Z P y X

def TauPt (X : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → TauPtAt U x V dict Z P y X

def SupBdWt (la : AllWt.Weight Dw) (β : ℝ) : Prop :=
  ∀ (σ : c.F →+* ℂ), ∀ z ∈ framesOn (U (goodOf c σ)) Z, ∀ f ∈ Cusp Z U la,
    homN (U (goodOf c σ)) x (wtOf Dw la 0) f z ^ 2 ≤ β * petOn U x V dict Z (wtOf Dw la 0) σ f ^ 2

def SupBd (β : ℝ) : Prop := SupBdWt U x V dict Z P.uc β

variable {U x V dict Z P}

theorem JacFin.mono {X X' : ℝ} (h : JacFin U Z P X) (e : X ≤ X') : JacFin U Z P X' :=
  fun K _ _ _ y hy => (h K y hy).mono e

theorem TauPt.mono {X X' : ℝ} (h : TauPt U x V dict Z P X) (e : X ≤ X') : TauPt U x V dict Z P X' :=
  fun K _ _ _ y hy => (h K y hy).mono e

theorem SupBdWt.mono {la : AllWt.Weight Dw} {β β' : ℝ} (h : SupBdWt U x V dict Z la β) (e : β ≤ β') :
    SupBdWt U x V dict Z la β' :=
  fun σ z hz f hf => (h σ z hz f hf).trans (mul_le_mul_of_nonneg_right e (sq_nonneg _))

theorem SupBd.mono {β β' : ℝ} (h : SupBd U x V dict Z P β) (e : β ≤ β') : SupBd U x V dict Z P β' := SupBdWt.mono h e

theorem supBd_iff_wt_zero {β : ℝ} : SupBd U x V dict Z P β ↔ SupBdWt U x V dict Z (P.wt 0) β := by
  rw [SupBd, WtPar.wt, zero_smul, add_zero]

theorem supBdWt_iff {la : AllWt.Weight Dw} {β : ℝ} (hβ : 0 ≤ β) : SupBdWt U x V dict Z la β ↔
    ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, bergCusp U x V dict Z (wtOf Dw la 0) σ z ≤ ENNReal.ofReal β :=
  forall₃_congr fun _ _ _ => (bergCusp_le_iff hβ).symm

theorem SupBdWt.of_bergOn {la : AllWt.Weight Dw} {β : ℝ} (hβ : 0 ≤ β)
    (hd : ∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom)
    (h : ∀ σ, GoodEmb c σ → ∀ z : FPt (U σ).X, (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      bergOn (U σ) (V σ) (dict σ) Z (wtOf Dw la 0) z ≤ ENNReal.ofReal β) : SupBdWt U x V dict Z la β :=
  (supBdWt_iff hβ).2 fun σ z hz => (bergCusp_le_bergOn (hd _ (goodEmb_goodOf c σ)) ⟨z.1, z.2, hz.1⟩).trans
    (h _ (goodEmb_goodOf c σ) ⟨z.1, z.2, hz.1⟩ hz)

theorem SupBdWt.nrm_sq_le {la : AllWt.Weight Dw} {β : ℝ} (h : SupBdWt U x V dict Z la β) {K : Type} [Field K]
    [Algebra c.F K] {y : FrPt Xo c K} (hy : LiesOn Z y) {ρ : K →+* ℂ} (F : InfFr U y ρ) {f : Rul Xo c}
    (hf : f ∈ Cusp Z U la) : F.nrm x (wtOf Dw la 0) f ^ 2 ≤
      β * petOn U x V dict Z (wtOf Dw la 0) (ρ.comp (algebraMap c.F K)) f ^ 2 :=
  h _ _ (F.mem_framesOn hy) f hf

end Statements

end GlobalTheory.CompHS
