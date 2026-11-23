import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFormDefiningValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.Mult

section Abstract

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isMultiHomog_pow' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero =>
    classical
    intro m hm k
    rw [pow_zero, show (1 : MRing ι) = MvPolynomial.monomial 0 1 from rfl, MvPolynomial.support_monomial] at hm
    simp at hm
    subst hm
    simp
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact Small.Fund.isMultiHomog_mul ih hf

theorem norm_le_of_small (y : (Σ k, ι k) → Ω) (A : HermLine ι) (a₀ D : K → ℤ) (ε σ : Ω) (τ N : ℕ)
    (hD : ∀ k, D k = τ * A.a k + N * a₀ k) (hS : IsSmallH (mCoordIdeal y) y A τ σ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {x W : ℂ}
    (hx : Small.HasVal y a₀ ε z x) (hW : Small.HasVal y D (σ * ε ^ N) z W) :
    ‖W‖ ≤ ‖x‖ ^ N * A.h z ^ τ := by
  obtain ⟨dg₀, dh₀, g₀, h₀, mg₀, mh₀, d₀, y₀, n₀, v₀⟩ := hx
  obtain ⟨dg, dh, g, h, mg, mh, d, yy, nz, v⟩ := hW
  have key := hS (dg + N • dh₀) (N • dg₀ + dh) (g * h₀ ^ N) (g₀ ^ N * h) z
    (Small.Fund.isMultiHomog_mul mg (isMultiHomog_pow' mh₀ N))
    (Small.Fund.isMultiHomog_mul (isMultiHomog_pow' mg₀ N) mh)
    (fun k => by
      have e1 := d k
      have e2 := d₀ k
      have e3 := hD k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [e1, e2, e3]
      ring)
    (by
      simp only [map_mul, map_pow]
      rw [yy, y₀]
      ring)
    hz
  have ev : ∀ f : MRing ι, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.aeval z f := by
    intro f
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  rw [ev, ev] at key
  simp only [map_mul, map_pow, norm_mul, norm_pow, v, v₀, mul_pow] at key
  have p1 : 0 < ‖MvPolynomial.aeval z h‖ := norm_pos_iff.2 nz
  have p2 : 0 < ‖MvPolynomial.aeval z h₀‖ ^ N := pow_pos (norm_pos_iff.2 n₀) N
  have h3 : ‖W‖ * (‖MvPolynomial.aeval z h‖ * ‖MvPolynomial.aeval z h₀‖ ^ N) ≤
      (‖x‖ ^ N * A.h z ^ τ) * (‖MvPolynomial.aeval z h‖ * ‖MvPolynomial.aeval z h₀‖ ^ N) := by
    calc _ = _ := by ring
      _ ≤ _ := key
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 (mul_pos p1 p2)

theorem mem_chartLatNm_mul (y : (Σ k, ι k) → Ω) (a a₀ D : K → ℤ) (τ N : ℕ) {σ ε : Ω}
    (hD : ∀ k, D k = τ * a k + N * a₀ k) (hσ : σ ∈ chartLatNm y a τ) (hε : ε ∈ chartLatNm y a₀ 1) :
    σ * ε ^ N ∈ chartLatNm y D 1 := by
  intro c hc
  have h3 := mul_mem (hσ c hc) (pow_mem (hε c hc) N)
  convert h3 using 1
  have h4 : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * D k)) = (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
      (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a₀ k))) ^ N := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast (y ⟨k, c k⟩ ^ _) N, ← zpow_mul, ← zpow_add₀ (hc k), hD k]
    congr 1
    push_cast
    ring
  rw [h4, mul_pow]
  ring

theorem nonzeroDefect_height_power_absorbs_constants {X Hh S t d W : ℝ} {τ q : ℕ} (hX : 0 ≤ X) (hH : 0 < Hh) (hS : 0 < S)
    (hb : X ≠ 0 → X ^ 8 * Hh ≤ Real.exp (q * d) * S ^ q)
    (hW : W ≤ X ^ (8 * τ) * (Real.exp (q * t) * Hh) ^ τ) :
    W ≤ Real.exp (((τ * q : ℕ) : ℝ) * (t + d)) * S ^ (τ * q) := by
  have hpos : 0 < Real.exp (((τ * q : ℕ) : ℝ) * (t + d)) * S ^ (τ * q) := by positivity
  rcases hX.eq_or_lt with h0 | h0
  · subst h0
    rcases Nat.eq_zero_or_pos τ with h1 | h1
    · subst h1
      simpa using hW
    · have : (0 : ℝ) ^ (8 * τ) = 0 := zero_pow (by omega)
      rw [this, zero_mul] at hW
      exact hW.trans hpos.le
  · have h2 := pow_le_pow_left₀ (by positivity) (hb h0.ne') τ
    have e1 : X ^ (8 * τ) * (Real.exp (q * t) * Hh) ^ τ = (X ^ 8 * Hh) ^ τ * Real.exp (q * t) ^ τ := by
      rw [pow_mul, mul_pow, mul_pow]
      ring
    have e2 : Real.exp (((τ * q : ℕ) : ℝ) * (t + d)) * S ^ (τ * q) =
        (Real.exp (q * d) * S ^ q) ^ τ * Real.exp (q * t) ^ τ := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, pow_mul' S]
      have : ((τ * q : ℕ) : ℝ) * (t + d) = τ * (q * d) + τ * (q * t) := by
        push_cast
        ring
      rw [this, Real.exp_add]
      ring
    rw [e2]
    rw [e1] at hW
    exact hW.trans (mul_le_mul_of_nonneg_right h2 (by positivity))

end Abstract

section Model

variable {Ψ : Type} [Fintype Ψ] {Nn : ℕ}

theorem coef_split (RM : Top.RootModel Ψ Nn) (lam nu : Top.Wt Ψ Nn) (s : ℝ) (j : Option (Ψ × Fin Nn)) :
    RM.coef (lam - s • nu) s j = RM.coef lam 0 j - s * RM.coef nu (-1) j := by
  cases j with
  | none =>
    simp only [Top.RootModel.coef]
    ring
  | some r =>
    simp only [Top.RootModel.coef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem line_a (RM : Top.RootModel Ψ Nn) (t t' : ℝ) (j : Option (Ψ × Fin Nn)) : (RM.line t j).a = (RM.line t' j).a := by
  cases j with
  | none => rfl
  | some r => exact (RM.x_deg t r).trans (RM.x_deg t' r).symm

theorem scaled_bound (RM : Top.RootModel Ψ Nn) (lam nu : Top.Wt Ψ Nn) {z : (Σ k, RM.ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (q q₀ : ℕ) (hq₀ : 0 < q₀) (s C S t : ℝ) (hS : 0 < S) (x : ℂ) (hx : x ≠ 0)
    (m : Option (Ψ × Fin Nn) → ℤ) (hq : (q : ℝ) * s = 8 * q₀)
    (hm : ∀ j, (m j : ℝ) = q * RM.coef (lam - s • nu) s j)
    (hI : s / q₀ * Real.log ‖x‖ + RM.weight t (lam - s • nu) s z ≤ C * s + Real.log S) :
    ‖x‖ ^ 8 * (Top.combLine (RM.line t) m).h z ≤ Real.exp (q * (C * s)) * S ^ q := by
  have hq₀R : (q₀ : ℝ) ≠ 0 := by exact_mod_cast hq₀.ne'
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hH : 0 < (Top.combLine (RM.line t) m).h z := (Top.combLine (RM.line t) m).pos z hz
  have hl : Real.log ((Top.combLine (RM.line t) m).h z) = ∑ j, (m j : ℝ) * Real.log ((RM.line t j).h z) := by
    show Real.log (∏ j, (RM.line t j).h z ^ m j) = _
    rw [Real.log_prod (fun j _ => zpow_ne_zero _ ((RM.line t j).pos z hz).ne')]
    simp only [Real.log_zpow]
  have e1 : Real.log (‖x‖ ^ 8 * (Top.combLine (RM.line t) m).h z) =
      q * (s / q₀ * Real.log ‖x‖ + RM.weight t (lam - s • nu) s z) := by
    rw [Real.log_mul (by positivity) hH.ne', Real.log_pow, hl]
    simp only [hm, Top.RootModel.weight, mul_add, Finset.mul_sum, mul_assoc]
    congr 1
    have : (q : ℝ) * (s / q₀ * Real.log ‖x‖) = (q * s) / q₀ * Real.log ‖x‖ := by ring
    rw [this, hq]
    field_simp
    norm_num
    ring
  have e2 : Real.exp (q * (C * s)) * S ^ q = Real.exp (q * (C * s + Real.log S)) := by
    rw [mul_add, Real.exp_add, Real.exp_nat_mul (Real.log S), Real.exp_log hS]
  rw [e2, ← Real.exp_log (show 0 < ‖x‖ ^ 8 * (Top.combLine (RM.line t) m).h z by positivity), e1]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg q))

end Model

section Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem nOf_smul (u : GlobalTheory.AllWt.Weight Dw) (k : ℕ) (j : Option (RootIx Dw)) : nOf (k • u) j = k * nOf u j := by
  cases j with
  | none => simp [nOf]
  | some r => simp [nOf]

theorem combLine_a_apply {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (k : K) : (Top.combLine ℓ n).a k = ∑ j, n j * (ℓ j).a k := by
  simp [Top.combLine, Finset.sum_apply]

theorem deg_eq (u : GlobalTheory.AllWt.Weight Dw) (n₀ m : Option (RootIx Dw) → ℤ) (q τ : ℕ) (t : ℝ)
    (hm : ∀ j, m j = q * nOf u j - 8 * n₀ j) (k : RM.K) :
    degOf RM ((τ * q) • u) k = τ * (Top.combLine (RM.line t) m).a k + ((8 * τ : ℕ) : ℤ) * (Top.combLine (RM.line 1) n₀).a k := by
  simp only [degOf, combLine_a_apply, nOf_smul, hm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [line_a RM t 1 j]
  push_cast
  ring

theorem step (Or : RootOrigin Y S RM Fx) (u : GlobalTheory.AllWt.Weight Dw) (nu : Top.Wt (CMType H) (Dw.p + Dw.q))
    {q₀ : ℕ} (hq₀ : 0 < q₀) {n₀ : Option (RootIx Dw) → ℤ} {ε : RM.Ω}
    (hεm : ε ∈ chartLatNm RM.y (Top.combLine (RM.line 1) n₀).a 1) {w e : MRing RM.ι}
    (hform : Small.IsFormOff (mCoordIdeal RM.y) (w * e))
    (hev : ∀ z : (Σ k, RM.ι k) → ℂ, MvPolynomial.aeval z e ≠ 0 →
      ∃ x, Small.HasVal RM.y (Top.combLine (RM.line 1) n₀).a ε z x)
    {C s t : ℝ} (q : ℕ) (hq : (q : ℝ) * s = 8 * q₀) (m : Option (RootIx Dw) → ℤ)
    (hmZ : ∀ j, m j = q * nOf u j - 8 * n₀ j)
    (hmR : ∀ j, (m j : ℝ) = q * RM.coef (reW u - s • nu) s j)
    (hI : ∀ z ∈ mcPts (mCoordIdeal RM.y), MvPolynomial.aeval z w ≠ 0 → ∀ x : ℂ,
      Small.HasVal RM.y (Top.combLine (RM.line 1) n₀).a ε z x → x ≠ 0 →
        s / q₀ * Real.log ‖x‖ + RM.weight (Top.scale s) (reW u - s • nu) s z ≤
          C * s + Real.log (∏ r, (Or.sing r).h z ^ nOf u (some r)))
    (τ : ℕ) (σ : RM.Ω) (hσ : σ ∈ chartLatNm RM.y (Top.combLine (RM.line (Top.scale s)) m).a τ)
    (hS : IsSmallH (mCoordIdeal RM.y) RM.y (Small.shiftH (Top.combLine (RM.line (Top.scale s)) m) (q * t)) τ σ) :
    σ * (ε ^ 8) ^ τ ∈ modelSmall Or ((τ * q) • u) (Real.exp (((τ * q : ℕ) : ℝ) * (t + C * s))) := by
  have hD : ∀ k, degOf RM ((τ * q) • u) k = τ * (Top.combLine (RM.line (Top.scale s)) m).a k +
      ((8 * τ : ℕ) : ℤ) * (Top.combLine (RM.line 1) n₀).a k := deg_eq u n₀ m q τ _ hmZ
  rw [← pow_mul]
  refine ⟨mem_chartLatNm_mul RM.y _ _ _ τ (8 * τ) hD hσ hεm, ?_⟩
  show HodgeLe Or _ _ _
  unfold HodgeLe
  refine ⟨w * e, hform, fun z hz hne W hW => ?_⟩
  rw [map_mul] at hne
  obtain ⟨x, hx⟩ := hev z (right_ne_zero_of_mul hne)
  have hb := norm_le_of_small RM.y (Small.shiftH (Top.combLine (RM.line (Top.scale s)) m) (q * t)) _ _ ε σ τ (8 * τ)
    hD hS hz hx hW
  have hSv : 0 < ∏ r, (Or.sing r).h z ^ nOf u (some r) :=
    Finset.prod_pos fun r _ => zpow_pos ((Or.sing r).pos z hz.1) _
  have hfin := nonzeroDefect_height_power_absorbs_constants (X := ‖x‖) (Hh := (Top.combLine (RM.line (Top.scale s)) m).h z)
    (S := ∏ r, (Or.sing r).h z ^ nOf u (some r)) (t := t) (d := C * s) (W := ‖W‖) (τ := τ) (q := q)
    (norm_nonneg _) ((Top.combLine (RM.line (Top.scale s)) m).pos z hz.1) hSv
    (fun h0 => scaled_bound RM (reW u) nu hz.1 q q₀ hq₀ s C _ _ hSv x (norm_ne_zero_iff.1 h0) m hq hmR
      (hI z hz (left_ne_zero_of_mul hne) x hx (norm_ne_zero_iff.1 h0))) hb
  have hprod : ∏ r, (Or.sing r).h z ^ nOf ((τ * q) • u) (some r) =
      (∏ r, (Or.sing r).h z ^ nOf u (some r)) ^ (τ * q) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [nOf_smul, mul_comm, zpow_mul, zpow_natCast]
  rw [hprod]
  exact hfin

end Step

theorem vs_mult : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ∃ (C : ℝ) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (RootIx Dw) → ℤ) (θ : ℕ → (T.M B b).Ω), 0 ≤ C ∧ (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧ (∀ n, 0 < q n ∧ 8 ∣ q n ∧ θ n ≠ 0) ∧ (∀ n j, (m n j : ℝ) = q n * (T.M B b).coef (T.lamS (reW u) (s n)) (s n) j) ∧ ∀ (n τ : ℕ) (t : ℝ), ∀ σ ∈ chartLatNm (T.M B b).y (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)).a τ, IsSmallH (mCoordIdeal (T.M B b).y) (T.M B b).y (Small.shiftH (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)) (q n * t)) τ σ → σ * θ n ^ τ ∈ modelSmall (o.toTowerOrigin.Or B b) ((τ * q n) • u) (Real.exp (((τ * q n : ℕ) : ℝ) * (t + C * s n))) := by
  intro _ E _ _ _ H Dw l Xo c Y _ T o B b u hu
  have hn' : ∀ j, (nOf u j : ℝ) = (T.M B b).coef (reW u) 0 j := by
    intro j
    cases j with
    | none => simp [nOf, Top.RootModel.coef]
    | some r => simp [nOf, Top.RootModel.coef, reW]
  have hreg : Top.RegDominant (reW u) := fun τ a b' h => by
    have := hu τ h
    simpa [reW] using this
  obtain ⟨q₀, n₀, ε, w, C, s₀, hq₀, hn₀, hε0, hεm, hw, hC, hs₀, hI⟩ :=
    GlobalTheory.T.good_origin_root_weight_bound E H Dw l Xo c Y T o B b (reW u) (nOf u) hn' hreg
  obtain ⟨e, he, hev⟩ := GlobalTheory.T.exists_form_defining_value _ _ _ (T.M B b).y (T.M B b).birational (T.M B b).arith.2.1.2.2
    (Top.combLine ((T.M B b).line 1) n₀).a ε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / s₀)
  have hform : Small.IsFormOff (mCoordIdeal (T.M B b).y) (w * e) := by
    obtain ⟨d₁, h₁⟩ := hw.1
    obtain ⟨d₂, h₂⟩ := he.1
    refine ⟨⟨_, Small.Fund.isMultiHomog_mul h₁ h₂⟩, fun h => ?_⟩
    have hp : (mCoordIdeal (T.M B b).y).IsPrime := RingHom.ker_isPrime _
    rcases hp.mem_or_mem h with h | h
    · exact hw.2 h
    · exact he.2 h
  let sq : ℕ → ℝ := fun n => 1 / (((n + N₀ : ℕ) : ℝ) + 1)
  let qq : ℕ → ℕ := fun n => 8 * q₀ * (n + N₀ + 1)
  have hsq : ∀ n, 0 < sq n := fun n => by positivity
  have hqs : ∀ n, (qq n : ℝ) * sq n = 8 * q₀ := by
    intro n
    simp only [qq, sq]
    push_cast
    field_simp
  have hsle : ∀ n, sq n ≤ s₀ := by
    intro n
    have h1 : 1 / s₀ < ((n + N₀ : ℕ) : ℝ) + 1 := by
      push_cast
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h2 := (div_lt_iff₀ hs₀).1 h1
    exact ((div_le_iff₀ (by positivity)).2 (by linarith))
  have hmR : ∀ n j, (((qq n : ℤ) * nOf u j - 8 * n₀ j : ℤ) : ℝ) =
      qq n * (T.M B b).coef (reW u - sq n • T.nu) (sq n) j := by
    intro n j
    rw [coef_split, ← hn', mul_sub, ← mul_assoc, hqs]
    push_cast
    rw [hn₀ j]
    ring
  refine ⟨C, sq, qq, fun n j => (qq n : ℤ) * nOf u j - 8 * n₀ j, fun _ => ε ^ 8, hC, hsq, ?_, ?_, hmR, ?_⟩
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat N₀)
  · intro n
    refine ⟨by simp only [qq]; positivity, ⟨q₀ * (n + N₀ + 1), by simp only [qq]; ring⟩, pow_ne_zero _ hε0⟩
  · intro n τ t σ hσ hS
    exact step (o.toTowerOrigin.Or B b) u T.nu hq₀ hεm hform (fun z hz => hev ℂ z hz) (qq n) (hqs n) _
      (fun _ => rfl) (hmR n) (fun z hz hwz x hx hx0 => hI (sq n) (hsq n) (hsle n) z hz hwz x hx hx0) τ σ hσ hS

end GlobalTheory.CompanionTheory.Ar.Plug.Mult
