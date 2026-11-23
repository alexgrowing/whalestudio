import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerOriginComponentBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormDegreeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFrameComponentBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionWeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormAllTowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LowHeightOfGivenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelSmallSectionsMulStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CountVolumePowerComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

open scoped ENNReal

theorem encard_le_pow_of_rel {α β : Type*} {A : Set α} {B : Set β} {d : ℕ} (hd : 0 < d)
    (P : α → Fin d → β → Prop) (hex : ∀ a ∈ A, ∀ i, ∃ b ∈ B, P a i b)
    (hinj : ∀ a ∈ A, ∀ a' ∈ A, (∀ i, ∃ b, P a i b ∧ P a' i b) → a = a') :
    A.encard ≤ B.encard ^ d := by
  classical
  rcases B.finite_or_infinite with hB | hB
  · choose F hF hP using hex
    haveI : Fintype B := hB.fintype
    let G : A → (Fin d → B) := fun a i => ⟨F a.1 a.2 i, hF a.1 a.2 i⟩
    have hG : Function.Injective G := fun a a' e => Subtype.ext (hinj a.1 a.2 a'.1 a'.2 fun i =>
      ⟨F a.1 a.2 i, hP a.1 a.2 i, by
        have : F a.1 a.2 i = F a'.1 a'.2 i := congrArg Subtype.val (congrFun e i)
        rw [this]; exact hP a'.1 a'.2 i⟩)
    have h1 : ENat.card A ≤ ENat.card (Fin d → B) := ENat.card_le_card_of_injective hG
    have h2 : ENat.card (Fin d → B) = ENat.card B ^ d := by
      simp [ENat.card_eq_coe_fintype_card, Fintype.card_fun]
    rw [h2] at h1
    exact h1
  · rw [hB.encard_eq, ENat.top_pow hd.ne']
    exact le_top

theorem ofReal_mul_le_of_forall_pos {A y : ℝ} {V : ℝ≥0∞} (H : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (A * (y - ε)) ≤ V) :
    ENNReal.ofReal (A * y) ≤ V := by
  have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal (A * (y - ε))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (A * y))) := by
    have h2 : Continuous fun ε : ℝ => ENNReal.ofReal (A * (y - ε)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_const.sub continuous_id))
    have h3 := (h2.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h3
  exact le_of_tendsto h1 (eventually_mem_nhdsWithin.mono fun ε hε => H ε hε)

section Val

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem vLa_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : vLa la (a * b) = vLa la a + vLa la b := by
  simp only [vLa, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

theorem vLa_one : vLa la (1 : K) = 0 := by simp [vLa]

theorem vLa_pow {a : K} (ha : a ≠ 0) (n : ℕ) : vLa la (a ^ n) = n * vLa la a := by
  induction n with
  | zero => simp [vLa_one]
  | succ n ih => rw [pow_succ, vLa_mul la (pow_ne_zero _ ha) ha, ih]; push_cast; ring

theorem vLa_natCast_nonneg {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have e : (n : K) = algebraMap (𝓞 K) K (n : 𝓞 K) := (map_natCast _ n).symm
  have h0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : la.valuation K (n : K) ≤ 1 := by rw [e]; exact la.valuation_le_one _
  have h2 : la.valuation K (n : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h3 := (WithZero.log_le_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at h3
  simp only [vLa]
  omega

theorem exists_prime_mem : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  haveI := la.isMaximal
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := la.asIdeal.finiteQuotientOfFreeOfNeBot la.ne_bot
  letI := Ideal.Quotient.field la.asIdeal
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ la.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem vLa_prod_ge {S : Finset ℕ} (hS : ∀ p ∈ S, p ≠ 0) (e : ℕ → ℕ) {q : ℕ} (hq : q ∈ S) :
    (e q : ℤ) * vLa la (q : K) ≤ vLa la (((∏ p ∈ S, p ^ e p : ℕ)) : K) := by
  have hM : (∏ p ∈ S.erase q, p ^ e p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p (Finset.mem_of_mem_erase hp))
  have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 (hS q hq)
  rw [← Finset.mul_prod_erase S _ hq, Nat.cast_mul, Nat.cast_pow,
    vLa_mul la (pow_ne_zero _ hq0) (Nat.cast_ne_zero.2 hM), vLa_pow la hq0]
  have := vLa_natCast_nonneg (K := K) la hM
  omega

end Val

section Num

variable (E : Type) [Field E] [NumberField E]

theorem exTwo_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ exTwo E p := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have h2 : 0 ≤ GlobalTheory.CovHt.htEx E p := by
    unfold GlobalTheory.CovHt.htEx
    have : 0 ≤ (p : ℝ) - 1 := by linarith
    positivity
  unfold exTwo
  split_ifs <;> linarith

end Num

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

variable (E) in

def clearN (S : Finset ℕ) (u : GlobalTheory.AllWt.Weight Dw) : ℕ := ∏ p ∈ S, p ^ ⌈2 * exTwo E p * GlobalTheory.CovHt.l1 u⌉₊

theorem clearN_ne_zero {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (u : GlobalTheory.AllWt.Weight Dw) : clearN E S u ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p hp).ne_zero

theorem weightAbsEntrySum_nonneg (u : GlobalTheory.AllWt.Weight Dw) : 0 ≤ GlobalTheory.CovHt.l1 u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem weightAbsEntrySum_nsmul (n : ℕ) (u : GlobalTheory.AllWt.Weight Dw) : GlobalTheory.CovHt.l1 (n • u) = n * GlobalTheory.CovHt.l1 u := by
  unfold GlobalTheory.CovHt.l1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [abs_mul]

theorem clearN_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (u : GlobalTheory.AllWt.Weight Dw) :
    (clearN E S u : ℝ) ≤
      Real.exp (2 * GlobalTheory.CovHt.l1 u * (∑ p ∈ S, exTwo E p * Real.log p) + ∑ p ∈ S, Real.log p) := by
  have e : 2 * GlobalTheory.CovHt.l1 u * (∑ p ∈ S, exTwo E p * Real.log p) + ∑ p ∈ S, Real.log p =
      ∑ p ∈ S, (2 * exTwo E p * GlobalTheory.CovHt.l1 u + 1) * Real.log (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e, Real.exp_sum, clearN, Nat.cast_prod]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_le
  have ha : 0 ≤ 2 * exTwo E p * GlobalTheory.CovHt.l1 u :=
    mul_nonneg (mul_nonneg zero_le_two (exTwo_nonneg E (hS p hp))) (weightAbsEntrySum_nonneg u)
  rw [Nat.cast_pow, ← Real.rpow_natCast, Real.rpow_def_of_pos hp0, Real.exp_le_exp, mul_comm]
  exact mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one ha).le (Real.log_nonneg hp1)

theorem strictAnti_nsmul {u : GlobalTheory.AllWt.Weight Dw} (h : ∀ τ, StrictAnti (u τ)) {n : ℕ} (hn : 0 < n) (τ) :
    StrictAnti ((n • u) τ) := fun a b hab => by
  have h1 := h τ hab
  have h2 : (0 : ℤ) < n := by exact_mod_cast hn
  simpa using mul_lt_mul_of_pos_left h1 h2

theorem clear_integral {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hHT : HTLow Xo c) {Bd : ℝ} {S : Finset ℕ}
    (hS : GlobalTheory.CompHt.htPrimes l Bd = ↑S) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (f : Rul Xo c)
    (hf : f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0))
    (hv : ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
      ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la,
        ((-((vLa la (p : c.F) : ℝ) * (if p ∈ S then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f) :
    ∀ la, ∀ w ∈ (GlobalTheory.CompHt.mixVals Xo c Bd).1 la, 0 ≤ w (((clearN E S u : ℕ) : c.F) • f) := by
  intro la w hw
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => by
    have : p ∈ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hp
    exact this.1
  obtain ⟨p, hp, hpl⟩ := exists_prime_mem la
  have hval := (GlobalTheory.CompHt.mixVals Xo c Bd).2 la w hw
  have hN0 := clearN_ne_zero (E := E) hSp u
  have hN : ((clearN E S u : ℕ) : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  rw [hval.smul _ _ hN]
  have hvN : 0 ≤ vLa la ((clearN E S u : ℕ) : c.F) := vLa_natCast_nonneg la hN0
  have hbot := hval.ne_bot f
  by_cases hpS : p ∈ S
  · have hpm : p ∈ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hpS
    rw [GlobalTheory.CompHt.mixVals_of_mem hpm hpl] at hw
    obtain ⟨v, hv', hle⟩ := hHT p la hp hpl w hw
    have h1 := hle u f ((GlobalTheory.AllWt.cuspOn_le U Z _).trans (GlobalTheory.AllWt.cuspW_le_secZ _) hf)
    have h2 := hv p la hp hpl v hv'
    rw [if_pos hpS] at h2
    have h3 := h2.trans h1
    have hvp : 0 ≤ vLa la (p : c.F) := vLa_natCast_nonneg la hp.ne_zero
    have h4 : (2 * ((vLa la (p : c.F) : ℝ) * exTwo E p * GlobalTheory.CovHt.l1 u)) ≤ (vLa la ((clearN E S u : ℕ) : c.F) : ℝ) := by
      have h5 := vLa_prod_ge (K := c.F) la (fun q hq => (hSp q hq).ne_zero)
        (fun q => ⌈2 * exTwo E q * GlobalTheory.CovHt.l1 u⌉₊) hpS
      have h6 : ((⌈2 * exTwo E p * GlobalTheory.CovHt.l1 u⌉₊ : ℕ) : ℝ) * (vLa la (p : c.F) : ℝ) ≤
          (vLa la ((clearN E S u : ℕ) : c.F) : ℝ) := by exact_mod_cast h5
      have h7 := Nat.le_ceil (2 * exTwo E p * GlobalTheory.CovHt.l1 u)
      have h8 : (0 : ℝ) ≤ (vLa la (p : c.F) : ℝ) := by exact_mod_cast hvp
      nlinarith [mul_le_mul_of_nonneg_right h7 h8]
    generalize w f = W at *
    induction W with
    | bot => exact absurd rfl hbot
    | top => rw [EReal.coe_add_top]; exact le_top
    | coe W =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h3
      rw [← EReal.coe_add]
      have : (0 : ℝ) ≤ (vLa la ((clearN E S u : ℕ) : c.F) : ℝ) + W := by linarith
      exact_mod_cast this
  · have hpm : p ∉ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hpS
    rw [GlobalTheory.CompHt.mixVals_of_not_mem hp hpm hpl] at hw
    have h2 := hv p la hp hpl w hw
    rw [if_neg hpS] at h2
    have h3 : (0 : EReal) ≤ w f := by simpa using h2
    refine add_nonneg ?_ h3
    exact_mod_cast hvN

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Tr

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

theorem trOf_sub (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) (a b : RM.Ω) :
    trOf Rd u (a - b) = trOf Rd u a - trOf Rd u b := by
  letI := Rd.φ.toAlgebra
  simp only [trOf, sub_div, map_sub]

end Tr

set_option synthInstance.maxHeartbeats 400000 in

theorem modelSmall_encard_le [IsGalois ℚ E] (hGv : Top.Given) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (hL : CompLaws U h e) (hUn : Ref.UnifAll Xo c) {x : ℝ}
    (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q))
    (o : Top.GoodOrigin Y T) (Bn : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or Bn b)) (Z : Comp Xo c)
    (Rd : Reading Fr h Z) (hGeo : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw) (hanti : ∀ τ, StrictAnti (u τ)) (hHT : HTLow Xo c) {Bd : ℝ}
    (hS : GlobalTheory.CompHt.htPrimes l Bd = ↑(o.toTowerOrigin.S Bn)) (hd : 0 < (o.toTowerOrigin.Or Bn b).Fl.deg)
    (k₀ : ℕ) (R₀ : ℝ) (hR₀ : 0 ≤ R₀) (f : Fin (o.toTowerOrigin.Or Bn b).Fl.deg → (T.M Bn b).Ω)
    (hfs : ∀ i, f i ∈ modelSmall (o.toTowerOrigin.Or Bn b) (k₀ • u) R₀)
    (hinj : ∀ (v : GlobalTheory.AllWt.Weight Dw) (s : (T.M Bn b).Ω), (∀ i, trOf Rd v (s * f i) = 0) → s = 0)
    (τ : ℕ) (hτ : 0 < τ) {R R' : ℝ} (hR : 0 ≤ R)
    (hnum : (clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℝ) *
      (((o.toTowerOrigin.Or Bn b).Fl.deg : ℝ) * (R * R₀)) ≤ R') :
    (modelSmall (o.toTowerOrigin.Or Bn b) (τ • u) R).encard ≤
      (GlobalTheory.CompHt.smallOn U x (GlobalTheory.CompHt.mixVals Xo c Bd) Z ((τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0) R').encard ^
        (o.toTowerOrigin.Or Bn b).Fl.deg := by
  have hG : (τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0 = GlobalTheory.AllWt.wtOf Dw ((τ + k₀) • u) 0 := by
    rw [GlobalTheory.CompHt.nsmul_wtOf]; simp
  rw [hG]
  have hSp : ∀ p ∈ o.toTowerOrigin.S Bn, p.Prime := fun p hp => by
    have : p ∈ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hp
    exact this.1
  have hN0 := clearN_ne_zero (E := E) hSp ((τ + k₀) • u)
  have hN : ((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  refine encard_le_pow_of_rel hd (fun s i (b' : GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw ((τ + k₀) • u) 0)) =>
    ∃ g : Rul Xo c, (b' : Rul Xo c) = ((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) • g ∧
      evC h Z g = trOf Rd ((τ + k₀) • u) (s * f i)) ?_ ?_
  · intro s hs i
    have hprod := GlobalTheory.T.model_small_sections_mul E H Dw l Xo c Y T o Bn b (τ • u) (k₀ • u) R R₀ hR hR₀ s hs (f i) (hfs i)
    rw [← add_nsmul] at hprod
    obtain ⟨g, hg, hev, hnorm, hval⟩ := GlobalTheory.T.uniform_norm_all_tower_bound hGv E H Dw l Xo c r U h e hL hUn x hx Y T o Bn b Fr Z Rd hGeo
      ((τ + k₀) • u) (R * R₀) (strictAnti_nsmul hanti (by omega)) (mul_nonneg hR hR₀) (s * f i) hprod
    refine ⟨⟨((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) • g, Submodule.smul_mem _ _ hg⟩,
      ⟨clear_integral U hHT hS Z _ g hg hval, fun σ hσ z hz => ?_⟩, g, rfl, hev⟩
    show GlobalTheory.AllWt.homN (U σ) x _ (((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) • g) z ≤ R'
    rw [GlobalTheory.FlatLine.homN_smul, map_natCast, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left (hnorm σ hσ z hz) (Nat.cast_nonneg _)).trans hnum
  · intro s _ s' _ Hs
    have h0 : s - s' = 0 := hinj ((τ + k₀) • u) (s - s') fun i => by
      obtain ⟨b', ⟨g, hb, he⟩, ⟨g', hb', he'⟩⟩ := Hs i
      have hgg : g = g' := by
        have h1 := congrArg (fun y => (((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F))⁻¹ • y) (hb.symm.trans hb')
        simpa only [inv_smul_smul₀ hN] using h1
      rw [sub_mul, trOf_sub, ← he, ← he', hgg, sub_self]
    exact sub_eq_zero.1 h0

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVolM

open GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

theorem slope_sub_cost_le_compVolSlope : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (g B : ℝ), (∀ τ, StrictAnti (u τ)) → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g ≤ B → ((T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u : ℝ) : EReal) ≤ GlobalTheory.CompHt.compVolSlope U x 8 (GlobalTheory.CompHt.mixVals Xo c B) Z u := by
  intro hNef hGv h6 E _ _ _ _ H Dw l Xo c r U h e hL hUn x hx Y _ T o κ II hCO hII hProp hT1 Z u g B hanti hW hB
  obtain ⟨-, hdeg, hpos⟩ := (GlobalTheory.T.uniform_norm_degree_bound hNef hGv E H Dw l Xo c r U h e hL x hx Y T o κ II hCO hII hProp hT1).1 Z u hanti
  have hBn : Top.bigB0 (reW u) g < (⌊B⌋₊ : ℝ) + 1 := lt_of_le_of_lt hB (Nat.lt_floor_add_one B)
  obtain ⟨Fr, Rd, hGeo⟩ := GlobalTheory.T.tower_origin_component_bound E H Dw l Xo c r U h e hL Y T o.toTowerOrigin κ hCO ⌊B⌋₊ Z
  obtain ⟨k₀, R₀, f, h8, hR₀, hfs, -, hinj⟩ := GlobalTheory.T.generic_frame_component_bound hGv E H Dw l Xo c h Y T o ⌊B⌋₊ (κ Z) Fr Z Rd II u g hII hT1 hW hBn
  have hHT : HTLow Xo c := GlobalTheory.T.low_height_of_given hGv E H Dw l Xo c
  have hdim : GlobalTheory.CompHt.dimFlag Dw = Top.dimFl (CMType H) (Dw.p + Dw.q) :=
    (GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M ⌊B⌋₊ (κ Z)) u).2.2.2.2.2.1
  have hS : GlobalTheory.CompHt.htPrimes l B = ↑(o.toTowerOrigin.S ⌊B⌋₊) := by
    ext p
    simp only [GlobalTheory.CompHt.htPrimes, Set.mem_setOf_eq, Finset.mem_coe, o.toTowerOrigin.S_iff, Top.RootTower.InS,
      o.toTowerOrigin.bad_iff]
    refine and_congr_right fun hp => or_congr (Nat.le_floor_iff' hp.ne_zero).symm ?_
    have key : ((p : ℤ) ∣ 2 * NumberField.discr E * (l.M' : ℤ)) ↔ p ∣ 2 * (NumberField.discr E).natAbs * l.M' := by
      rw [Int.natCast_dvd]; simp [Int.natAbs_mul]
    exact ⟨fun hd => ⟨hp, key.2 hd⟩, fun hd => key.1 hd.2⟩
  have hδ := (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).δ_eq
  have hδpos := (T.M ⌊B⌋₊ (κ Z)).δ_pos
  have hn : 0 < Module.finrank ℚ c.F := Module.finrank_pos
  have hd : 0 < (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg := by
    rw [hδ] at hδpos; exact Nat.pos_of_mul_pos_left hδpos
  have hSp : ∀ p ∈ o.toTowerOrigin.S ⌊B⌋₊, p.Prime := fun p hp => by
    have : p ∈ GlobalTheory.CompHt.htPrimes l B := by rw [hS]; exact hp
    exact this.1
  have hcost : costTwo (E := E) l B = ∑ p ∈ o.toTowerOrigin.S ⌊B⌋₊, exTwo E p * Real.log p := by
    rw [costTwo, hS, finsum_mem_coe_finset]
  rw [GlobalTheory.CompHt.le_compVolSlope_iff U x 8 _ hpos]
  intro t
  have e0 : (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u) + t =
      (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u + t) := rfl
  refine ofReal_mul_le_of_forall_pos fun ε hε => ?_
  set t' : ℝ := t - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u - ε with ht'
  have hcount := GlobalTheory.T.full_intersection_weight_bound hGv h6 E H Dw l Xo c Y T o ⌊B⌋₊ (κ Z) II u g hII hT1 hW hBn t'
  have hev : ∀ᶠ τ : ℕ in atTop, (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard ≤
      (GlobalTheory.CompHt.smallOn U x (GlobalTheory.CompHt.mixVals Xo c B) Z ((τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0)
        (Real.exp (((τ + k₀ : ℕ) : ℝ) * t))).encard ^ (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg := by
    set cc : ℝ := costTwo (E := E) l B with hcc
    set L : ℝ := GlobalTheory.CovHt.l1 u with hLdef
    set d : ℝ := ((o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg : ℝ) with hdd
    set C : ℝ := ∑ p ∈ o.toTowerOrigin.S ⌊B⌋₊, Real.log p with hC
    have hd0 : 0 < d := by rw [hdd]; exact_mod_cast hd
    have hlim : ∀ᶠ τ : ℕ in atTop,
        (2 * (k₀ : ℝ) * L * cc + C + Real.log (d * R₀) - k₀ * t) ≤ (τ : ℝ) * ε := by
      have := tendsto_natCast_atTop_atTop (R := ℝ)
      exact (this.atTop_mul_const hε).eventually_ge_atTop _
    filter_upwards [hlim, eventually_gt_atTop 0] with τ hτ1 hτ0
    refine modelSmall_encard_le hGv U h e hL hUn hx Y T o ⌊B⌋₊ (κ Z) Fr Z Rd hGeo u hanti hHT hS hd k₀ R₀ hR₀.le f hfs hinj τ hτ0
      (Real.exp_pos _).le ?_
    have h1 := clearN_le (E := E) hSp ((τ + k₀) • u)
    rw [weightAbsEntrySum_nsmul, ← hcost, ← hLdef, ← hC] at h1
    have hdR : 0 < d * R₀ := mul_pos hd0 hR₀
    have h2 : d * (Real.exp (τ * t') * R₀) = Real.exp (τ * t' + Real.log (d * R₀)) := by
      rw [Real.exp_add, Real.exp_log hdR]; ring
    rw [h2]
    refine (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add, Real.exp_le_exp, ht']
    push_cast
    nlinarith [hτ1]
  have hshift := GlobalTheory.T.count_volume_power_comparison (GlobalTheory.CompHt.dimFlag Dw) (Module.finrank ℚ c.F) (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg k₀
    (fun τ => (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard)
    (fun τ => (GlobalTheory.CompHt.smallOn U x (GlobalTheory.CompHt.mixVals Xo c B) Z (τ • GlobalTheory.AllWt.wtOf Dw u 0) (Real.exp (τ * t))).encard)
    hn hd h8 hev
  have hc2 : GlobalTheory.CompHt.countVol (Top.dimFl (CMType H) (Dw.p + Dw.q)) (T.M ⌊B⌋₊ (κ Z)).δ 8
      (fun τ => (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard) =
      GlobalTheory.CompHt.countVol (GlobalTheory.CompHt.dimFlag Dw) (Module.finrank ℚ c.F * (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg) 8
      (fun τ => (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard) := by
    rw [hdim, hδ]
  have e1 : GlobalTheory.CompHt.topDeg U Z u * (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u + t - ε) =
      T.vol (κ Z) * Top.flagDeg (reW u) * (T.slope II ⌊B⌋₊ (κ Z) (reW u) + t') := by
    rw [hdeg, ht']; ring
  rw [e1]
  exact hcount.trans (hc2.le.trans hshift)

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVolM

theorem _root_.GlobalTheory.CompanionTheory.Relay.uniform_all_norm_height_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (g B : ℝ), (∀ τ, StrictAnti (u τ)) → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g ≤ B → ((T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u : ℝ) : EReal) ≤ GlobalTheory.CompHt.compVolSlope U x 8 (GlobalTheory.CompHt.mixVals Xo c B) Z u :=
  GlobalTheory.CompanionTheory.Ar.Plug.SlopeVolM.slope_sub_cost_le_compVolSlope
