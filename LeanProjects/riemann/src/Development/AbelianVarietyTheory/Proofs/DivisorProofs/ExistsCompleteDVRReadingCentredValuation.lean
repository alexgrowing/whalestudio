import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtOrd
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.RegularityFirstClauseBot
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

noncomputable section

namespace GlobalTheory.CentredDiscreteRead

open IsLocalRing

theorem eq_one_of_mul_eq_one {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) :
    a = 1 := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact zero_ne_one h
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact zero_ne_one h
  have h1 := congrArg WithZero.log h
  rw [WithZero.log_mul ha0 hb0, WithZero.log_one] at h1
  have h2 := (WithZero.log_le_log ha0 one_ne_zero).2 ha
  have h3 := (WithZero.log_le_log hb0 one_ne_zero).2 hb
  rw [WithZero.log_one] at h2 h3
  have h4 : WithZero.log a = 0 := by omega
  rw [← WithZero.exp_log ha0, h4, WithZero.exp_zero]

section Field

variable {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))

theorem val_eq_one_of_isUnit {y : v.valuationSubring} (hy : IsUnit y) : v (y : K) = 1 := by
  obtain ⟨u, rfl⟩ := hy
  refine eq_one_of_mul_eq_one (b := v ((u⁻¹ : (v.valuationSubring)ˣ) : K)) ((v.mem_valuationSubring_iff _).1 u.1.2)
    ((v.mem_valuationSubring_iff _).1 (u⁻¹).1.2) ?_
  rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]

theorem isUnit_of_val_eq_one {y : v.valuationSubring} (hy : v (y : K) = 1) : IsUnit y := by
  have h0 : (y : K) ≠ 0 := by intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have hm : (y : K)⁻¹ ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hy, inv_one]
  refine ⟨⟨y, ⟨_, hm⟩, ?_, ?_⟩, rfl⟩ <;> ext <;> simp [h0]

end Field

section Field

variable {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))

theorem log_val_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    WithZero.log (v (x * y)) = WithZero.log (v x) + WithZero.log (v y) := by
  rw [map_mul, WithZero.log_mul ((v.ne_zero_iff).2 hx) ((v.ne_zero_iff).2 hy)]

theorem log_val_zpow (x : K) (k : ℤ) : WithZero.log (v (x ^ k)) = k * WithZero.log (v x) := by
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]

theorem exists_dvr (hv : ∃ x : K, v x ≠ 0 ∧ v x < 1) :
    ∃ (_ : IsDiscreteValuationRing v.valuationSubring) (d : ℕ), 0 < d ∧
      ∀ y : v.valuationSubring, y ≠ 0 →
        -WithZero.log (v (y : K)) = (d : ℤ) * vV v.valuationSubring (algebraMap v.valuationSubring K y) := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ x : K, x ≠ 0 ∧ -WithZero.log (v x) = n := by
    obtain ⟨x, hx0, hx1⟩ := hv
    have hx : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
    have hl : WithZero.log (v x) < 0 := by
      have := (WithZero.log_lt_log hx0 one_ne_zero).2 hx1
      rwa [WithZero.log_one] at this
    exact ⟨(-WithZero.log (v x)).toNat, by omega, x, hx, by omega⟩
  set d := Nat.find hex with hd_def
  obtain ⟨hd, π, hπ0, hπ⟩ := Nat.find_spec hex
  rw [← hd_def] at hd hπ
  have hmin : ∀ n : ℕ, 0 < n → n < d → ∀ x : K, x ≠ 0 → -WithZero.log (v x) ≠ n :=
    fun n hn hnd x hx h => Nat.find_min hex hnd ⟨hn, x, hx, h⟩
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd

  have hdvd : ∀ x : K, x ≠ 0 → (d : ℤ) ∣ WithZero.log (v x) := by
    intro x hx
    set k := -WithZero.log (v x) with hk
    have hr0 := Int.emod_nonneg k hdz.ne'
    have hrd := Int.emod_lt_of_pos k hdz
    have hkq : k % d = k - d * (k / d) := Int.emod_def k d
    have hy0 : x * π ^ (-(k / d)) ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
    have hy : -WithZero.log (v (x * π ^ (-(k / d)))) = k % d := by
      rw [log_val_mul v hx (zpow_ne_zero _ hπ0), log_val_zpow]
      have : WithZero.log (v π) = -(d : ℤ) := by omega
      rw [this]; linarith
    have hr : k % d = 0 := by
      by_contra hne
      exact hmin (k % d).toNat (by omega) (by omega) _ hy0 (by rw [hy]; omega)
    have : (d : ℤ) ∣ k := Int.dvd_of_emod_eq_zero hr
    rw [hk] at this
    exact (dvd_neg).1 this
  have hπle : v π ≤ 1 := by
    have h1 : WithZero.log (v π) ≤ WithZero.log 1 := by rw [WithZero.log_one]; omega
    exact (WithZero.log_le_log ((v.ne_zero_iff).2 hπ0) one_ne_zero).1 h1
  set O := v.valuationSubring
  let ϖ : O := ⟨π, (v.mem_valuationSubring_iff _).2 hπle⟩
  have hϖ0 : ϖ ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)

  have hfac : ∀ y : O, y ≠ 0 → ∃ (n : ℕ) (u : Oˣ), (u : O) * ϖ ^ n = y ∧
      -WithZero.log (v (y : K)) = (d : ℤ) * n := by
    intro y hy
    have hy' : (y : K) ≠ 0 := fun h => hy (Subtype.ext h)
    obtain ⟨m, hm⟩ := hdvd _ hy'
    have hle : WithZero.log (v (y : K)) ≤ 0 := by
      have := (WithZero.log_le_log ((v.ne_zero_iff).2 hy') one_ne_zero).2 ((v.mem_valuationSubring_iff _).1 y.2)
      rwa [WithZero.log_one] at this
    have hm0 : m ≤ 0 := by
      by_contra h; push_neg at h
      have : (0 : ℤ) < d * m := mul_pos hdz h
      omega
    set n := (-m).toNat with hn
    have hnm : (n : ℤ) = -m := by omega
    have hpn : π ^ n ≠ 0 := pow_ne_zero _ hπ0
    set w : K := (y : K) / π ^ n
    have hw0 : w ≠ 0 := div_ne_zero hy' hpn
    have hwy : w * π ^ n = y := div_mul_cancel₀ _ hpn
    have hlw : WithZero.log (v w) = 0 := by
      have h1 := log_val_mul v hw0 hpn
      rw [hwy, map_pow, WithZero.log_pow, nsmul_eq_mul, hm] at h1
      have : WithZero.log (v π) = -(d : ℤ) := by omega
      rw [this] at h1
      have : (d : ℤ) * m = WithZero.log (v w) + n * -(d : ℤ) := h1
      rw [hnm] at this
      linarith
    have hvw : v w = 1 := by rw [← WithZero.exp_log ((v.ne_zero_iff).2 hw0), hlw, WithZero.exp_zero]
    have hwO : w ∈ O := (v.mem_valuationSubring_iff _).2 hvw.le
    have hu := isUnit_of_val_eq_one v (y := ⟨w, hwO⟩) hvw
    refine ⟨n, hu.unit, ?_, ?_⟩
    · ext
      simp only [IsUnit.unit_spec, Subring.coe_mul, Subring.coe_pow]
      exact hwy
    · rw [hm, hnm]; ring
  have hlogϖ : -WithZero.log (v (ϖ : K)) = d := hπ
  have hirr : Irreducible ϖ := by
    refine ⟨fun h => ?_, fun a b hab => ?_⟩
    · have := val_eq_one_of_isUnit v h
      have h1 : WithZero.log (v (ϖ : K)) = 0 := by
        rw [this, WithZero.log_one]
      omega
    · have ha : a ≠ 0 := by rintro rfl; rw [zero_mul] at hab; exact hϖ0 hab
      have hb : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hϖ0 hab
      obtain ⟨n, u, hu, hn⟩ := hfac a ha
      obtain ⟨m, u', hu', hm⟩ := hfac b hb
      have ha' : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
      have hb' : (b : K) ≠ 0 := fun h => hb (Subtype.ext h)
      have h1 : (ϖ : K) = (a : K) * b := by rw [hab]; rfl
      have h2 := log_val_mul v ha' hb'
      rw [← h1] at h2
      have h3 : (d : ℤ) = d * n + d * m := by linarith
      have h4 : (n : ℤ) + m = 1 := by
        have : (d : ℤ) * (n + m - 1) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · omega
        · omega
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · left; rw [← hu, h0, pow_zero, mul_one]; exact u.isUnit
      · right
        have : m = 0 := by omega
        rw [← hu', this, pow_zero, mul_one]; exact u'.isUnit
  haveI hdvr : IsDiscreteValuationRing O :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨ϖ, hirr, fun {y} hy => by
        obtain ⟨n, u, hu, -⟩ := hfac y hy
        exact ⟨n, ⟨u, by rw [← hu, mul_comm]⟩⟩⟩
  refine ⟨hdvr, d, hd, fun y hy => ?_⟩
  obtain ⟨n, u, hu, hn⟩ := hfac y hy
  rw [hn, ← hu, vV_alg_of_addVal (IsDiscreteValuationRing.addVal_def' u hirr n)]

end Field

section Completion

theorem vV_completion (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    {K : Type} [Field K] [Algebra O K] [IsFractionRing O K] {y : O} (hy : y ≠ 0) :
    vV (GlobalTheory.CountableCompletion.completionCDVR O).V
        (algebraMap _ (GlobalTheory.CountableCompletion.completionCDVR O).Fr
          (algebraMap O (GlobalTheory.CountableCompletion.completionCDVR O).V y)) = vV O (algebraMap O K y) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ' : Irreducible (algebraMap O (AdicCompletion (maximalIdeal O) O) π) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, AdicCompletion.maximalIdeal_eq_map, hπ.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  have hval := addVal_map_of_unr (algebraMap O (AdicCompletion (maximalIdeal O) O)) ⟨π, hπ, hπ'⟩ y
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 hy)
  rw [vV_alg_of_addVal (hval.trans hn.symm), vV_alg_of_addVal hn.symm]

end Completion

theorem exists_cdvr_read :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
      (ν : Valuation R (WithZero (Multiplicative ℤ))), (∀ a, ν a ≤ 1) →
      (∀ a ∈ IsLocalRing.maximalIdeal R, ν a < 1) → (∀ a, ν a = 0 → a = 0) →
      ∃ (T : Formalism.L2.Pj.CDVR) (g : R →+* T.V) (ρ : ℝ), 0 < ρ ∧ Function.Injective g ∧
        (∀ a ∈ IsLocalRing.maximalIdeal R, g a ∈ IsLocalRing.maximalIdeal T.V) ∧
        ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) =
          ρ * (Formalism.L2.Pj.vV T.V (algebraMap T.V T.Fr (g a)) : ℝ) := by
  intro R _ _ _ _ ν hle hlt hz
  by_cases hm : maximalIdeal R = ⊥
  ·
    have hF : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.2 hm
    letI : Field R := hF.toField
    let T := GlobalTheory.TrivialValuationTest.powerSeriesCDVR R
    let g : R →+* T.V := PowerSeries.C
    have hg : Function.Injective g := PowerSeries.C_injective
    refine ⟨T, g, 1, one_pos, hg, fun a ha => ?_, fun a ha => ?_⟩
    · rw [hm, Ideal.mem_bot] at ha
      rw [ha, map_zero g]
      exact Ideal.zero_mem _
    · have ha0 : a ≠ 0 := by rintro rfl; exact ha (map_zero ν)
      obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
      have hinv : ν a * ν b = 1 := by rw [← map_mul, hb, map_one]
      have h1 : ν a = 1 := eq_one_of_mul_eq_one (hle a) (hle _) hinv
      have hua : IsUnit a := ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩
      have hu : IsUnit (g a) := hua.map g
      have h2 := vV_unit_alg (V := T.V) (F := T.Fr) hu.unit
      rw [IsUnit.unit_spec] at h2
      rw [h1, WithZero.log_one, h2]
      simp
  ·
    obtain ⟨a0, ha0m, ha00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    have hS : nonZeroDivisors R ≤ ν.supp.primeCompl := fun x hx hsupp =>
      nonZeroDivisors.ne_zero hx (hz x ((Valuation.mem_supp_iff ν x).1 hsupp))
    let w : Valuation (FractionRing R) (WithZero (Multiplicative ℤ)) := ν.extendToLocalization hS (FractionRing R)
    have hw : ∀ a, w (algebraMap R (FractionRing R) a) = ν a :=
      Valuation.extendToLocalization_apply_map_apply ν hS (FractionRing R)
    obtain ⟨hdvr, d, hd, hread⟩ := exists_dvr w ⟨algebraMap R (FractionRing R) a0,
      by rw [hw]; exact fun h => ha00 (hz a0 h), by rw [hw]; exact hlt a0 ha0m⟩
    set O := w.valuationSubring
    haveI : CharZero (FractionRing R) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
    haveI : CharZero O := (algebraMap O (FractionRing R)).charZero
    let ι : R →+* O := (algebraMap R (FractionRing R)).codRestrict O fun a =>
      (w.mem_valuationSubring_iff _).2 (by rw [hw]; exact hle a)
    have hι : ∀ a, ((ι a : O) : FractionRing R) = algebraMap R (FractionRing R) a := fun _ => rfl
    have hιinj : Function.Injective ι := fun a b h =>
      IsFractionRing.injective R (FractionRing R) (by rw [← hι, ← hι, h])
    let T := GlobalTheory.CountableCompletion.completionCDVR O
    have hTinj : Function.Injective (algebraMap O T.V) := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr O
    refine ⟨T, (algebraMap O T.V).comp ι, d, by exact_mod_cast hd, hTinj.comp hιinj, fun a ha => ?_,
      fun a ha => ?_⟩
    · rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : IsUnit (ι a) := isUnit_of_map_unit (algebraMap O T.V) _ hu
      have h2 := val_eq_one_of_isUnit w h1
      rw [hι, hw] at h2
      exact (hlt a ha).ne h2
    · have ha0 : a ≠ 0 := by rintro rfl; exact ha (map_zero ν)
      have hιa : ι a ≠ 0 := fun h => ha0 (hιinj (h.trans (map_zero ι).symm))
      rw [RingHom.comp_apply, vV_completion O (K := FractionRing R) hιa]
      have h1 := hread (ι a) hιa
      rw [hι, hw] at h1
      have h2 : ((-(WithZero.log (ν a)) : ℤ) : ℝ) =
          (((d : ℤ) * vV O (algebraMap O (FractionRing R) (ι a)) : ℤ) : ℝ) := by rw [h1]
      push_cast at h2 ⊢
      linarith

end GlobalTheory.CentredDiscreteRead
