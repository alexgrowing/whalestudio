import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLocalGaussSumNormSqEqAbsNormPow

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

noncomputable section

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem pow_apply_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (x : Ideles E) : ((ξ.1 x : ℂˣ) : ℂ) ^ N = 1 := by
  have h1 : ((ξ ^ N : HChar E).1 x) = (ξ.1 x) ^ N := by
    rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rw [← Units.val_pow_eq_pow_val, ← h1, h]
  rfl

theorem locK_pow_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ((ξ.locK w x : ℂˣ) : ℂ) ^ N = 1 :=
  pow_apply_eq_one h _

theorem isUnitary_of_orderDvd {ξ : HChar E} {N : ℕ} (hN : 0 < N) (h : ξ.OrderDvd N) : IsUnitary ξ := fun x =>
  Complex.norm_eq_one_of_pow_eq_one (pow_apply_eq_one h x) hN.ne'

theorem expAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.UnrAt w) (hξ : ExpAt ξ w a) :
    ExpAt (χ * ξ) w a := by
  intro k
  have hk : χ.LevelLe w k := hχ.levelLe k
  refine ⟨fun hx => (hξ k).1 ?_, fun hn => hk.mul ((hξ k).2 hn)⟩
  have := hk.inv.mul hx
  rwa [inv_mul_cancel_left] at this

theorem psiAt_natMul (w : HeightOneSpectrum (𝓞 E)) (t : w.adicCompletion E) (k : ℕ) :
    psiAt w ((k : w.adicCompletion E) * t) = psiAt w t ^ k := by
  induction k with
  | zero => simpa using psiAt_eq_one (w := w) (t := 0) (by simp)
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, psiAt_add, ih, pow_succ]

theorem gaussSumAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w) {a : ℕ} (ha : a ≠ 0) (c : Eˣ) :
    gaussSumAt (χ * ξ) w a c = gaussSumAt ξ w a c := by
  unfold gaussSumAt
  congr 1
  funext y
  have hy := out_notMem w ha y
  have hy1 : w.valuation E ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) = 1 :=
    (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have hz0 : ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) ≠ 0 := fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  rw [gaussTerm, gaussTerm, dif_neg hz0, dif_neg hz0]
  have h1 : χ.locK w (Units.mk0 _ hz0) = 1 := by
    refine hχ _ ?_
    show Valued.v (((atFin w (Units.mk0 _ hz0)) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_mk0]
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval, hy1]
  have e : (χ * ξ).locK w (Units.mk0 _ hz0) = χ.locK w (Units.mk0 _ hz0) * ξ.locK w (Units.mk0 _ hz0) := rfl
  rw [e, h1, one_mul]

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem exists_gaussSumAt_dvd {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {q N : ℕ} (hq : q.Prime) (hqw : Ideal.absNorm w.asIdeal = q) (hN : 0 < N) (hξN : ξ.OrderDvd N) (hξ : ExpAt ξ w 1)
    (hξK : ∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) (hqK : ∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) :
    ∃ g : 𝓞 K, σ (g : K) = gaussSumAt ξ w 1 (unif w ^ (1 + diffExp w)) ∧ g ∣ (q : 𝓞 K) := by
  classical
  set c : Eˣ := unif w ^ (1 + diffExp w) with hc
  haveI : Fintype (𝓞 E ⧸ w.asIdeal ^ 1)ˣ := Fintype.ofFinite _
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hqv : w.valuation E ((q : 𝓞 E) : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have h := valuation_sub_le (w := w) (a := 1) (y := (q : 𝓞 E)) (y' := 0)
      (by rw [sub_zero, pow_one, ← hqw]; exact Ideal.absNorm_mem _)
    simpa using h
  have hterm : ∀ y : (𝓞 E ⧸ w.asIdeal ^ 1)ˣ, ∃ x : K,
      σ x = gaussTerm ξ w c ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1) : 𝓞 E) : E) ∧ x ^ (N * q) = 1 := by
    intro y
    have hy := out_notMem w one_ne_zero y
    set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1)
    have hy1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
    have hz0 : (z : E) ≠ 0 := fun h => by
      rw [h, map_zero] at hy1
      exact zero_ne_one hy1
    rw [gaussTerm, dif_neg hz0]
    obtain ⟨x1, hx1⟩ := hξK (Units.mk0 _ hz0)⁻¹
    have hp : psiAt w (algebraMap E (w.adicCompletion E) ((z : E) / c)) ^ q = 1 := by
      rw [← psiAt_natMul]
      apply psiAt_eq_one
      have e : ((q : ℕ) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) ((z : E) / c) =
          algebraMap E (w.adicCompletion E) (((q : 𝓞 E) : E) * ((z : E) / c)) := by simp
      rw [e, hval, map_mul, map_div₀, hy1, hc, valuation_unif_pow, one_div, ← div_eq_mul_inv,
        div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
      convert hqv using 2
      push_cast
      ring
    obtain ⟨x2, hx2⟩ := hqK _ hp
    have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
    have hx2q : x2 ^ q = 1 := σ.injective (by rw [map_pow, hx2, hp, map_one])
    refine ⟨x1 * x2, by rw [map_mul, hx1, hx2, map_inv], ?_⟩
    rw [mul_pow, pow_mul, hx1N, one_pow, one_mul, mul_comm N q, pow_mul, hx2q, one_pow]
  choose X hX using hterm
  have hpos : 0 < N * q := Nat.mul_pos hN hq.pos
  have hXi : ∀ y, IsIntegral ℤ (X y) := fun y => IsIntegral.of_pow hpos (by rw [(hX y).2]; exact isIntegral_one)
  have hXi' : ∀ y, IsIntegral ℤ (X y)⁻¹ := fun y =>
    IsIntegral.of_pow hpos (by rw [inv_pow, (hX y).2, inv_one]; exact isIntegral_one)
  have hnorm : ∀ y, ‖σ (X y)‖ = 1 := fun y =>
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, (hX y).2, map_one]) hpos.ne'
  have hgi : IsIntegral ℤ (∑ y, X y) := IsIntegral.sum _ fun y _ => hXi y
  have hgi' : IsIntegral ℤ (∑ y, (X y)⁻¹) := IsIntegral.sum _ fun y _ => hXi' y
  have hσg : σ (∑ y, X y) = gaussSumAt ξ w 1 c := by
    rw [map_sum, gaussSumAt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun y _ => (hX y).1
  have hσg' : σ (∑ y, (X y)⁻¹) = starRingEnd ℂ (gaussSumAt ξ w 1 c) := by
    rw [← hσg, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [map_inv₀, Complex.inv_eq_conj (hnorm y)]
  have hu : IsUnitary ξ := isUnitary_of_orderDvd hN hξN
  have hG := GlobalTheory.GaussMod.gaussSumAt_normSq ξ w 1 c one_ne_zero hξ hu (valuation_unif_pow w _)
  have hprod : (∑ y, X y) * (∑ y, (X y)⁻¹) = (q : K) := σ.injective (by
    rw [map_mul, hσg, hσg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hG, hqw, map_natCast]
    push_cast
    ring)
  refine ⟨⟨_, hgi⟩, hσg, ⟨⟨_, hgi'⟩, RingOfIntegers.ext ?_⟩⟩
  have e : ((q : 𝓞 K) : K) = (q : K) := by simp
  rw [e, ← hprod]
  rfl

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

theorem locEps_tame_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  intro E _ _ K _ _ _ σ χ ξ w q m N s hq hcard hqm hN hξN hχ hξ hξK hqK hs
  have hqw : Ideal.absNorm w.asIdeal = q := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hcard
  refine ⟨expAt_unr_mul hχ hξ, ?_⟩
  obtain ⟨gG, hgG, hdvd⟩ := exists_gaussSumAt_dvd σ hq hqw hN hξN hξ hξK hqK
  obtain ⟨x1, hx1⟩ := hξK (unif w ^ (1 + diffExp w))
  have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
  have hx1i : IsIntegral ℤ x1 := IsIntegral.of_pow hN (by rw [hx1N]; exact isIntegral_one)
  set a1 : 𝓞 K := ⟨x1, hx1i⟩ with ha1d
  have ha1 : IsUnit a1 := by
    have e : ((a1 : 𝓞 K) : K) = x1 := rfl
    exact IsUnit.of_pow_eq_one (RingOfIntegers.ext (by push_cast; exact (congrArg (· ^ N) e).trans hx1N)) hN.ne'
  have hqm' : (q : 𝓞 K) ∣ (m : 𝓞 K) := Nat.cast_dvd_cast hqm
  refine ⟨x1 * (q : K) ^ (-s).toNat * (gG : K), ?_, ?_⟩
  · have h1 : GlobalTheory.Square.IsAwayUnit m x1 := GlobalTheory.Square.IsAwayUnit.of_dvd (a := a1) (k := 0) (by simpa using ha1.dvd)
    have h2 : GlobalTheory.Square.IsAwayUnit m ((q : K) ^ (-s).toNat) := by
      have := GlobalTheory.Square.IsAwayUnit.of_dvd (K := K) (m := m) (a := (q : 𝓞 K) ^ (-s).toNat) (pow_dvd_pow_of_dvd hqm' _)
      simpa using this
    have h3 : GlobalTheory.Square.IsAwayUnit m (gG : K) := GlobalTheory.Square.IsAwayUnit.of_dvd (k := 1) (by rw [pow_one]; exact hdvd.trans hqm')
    exact (h1.mul h2).mul h3
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hj : (((-s).toNat : ℕ) : ℂ) = -(s : ℂ) := by
      have : (((-s).toNat : ℕ) : ℤ) = -s := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have e1 : ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((1 + diffExp w : ℕ) : ℂ)) =
        ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((0 + diffExp w : ℕ) : ℂ)) * (q : ℂ) ^ ((-s).toNat) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, hj]
      congr 1
      push_cast
      ring
    have e2 : (χ * ξ).locK w (unif w ^ (1 + diffExp w)) =
        χ.val w * χ.locK w (unif w ^ (0 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) := by
      show χ.locK w (unif w ^ (1 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) = _
      rw [pow_add, pow_one, map_mul, zero_add]
      rfl
    rw [locEps, locEps, if_neg one_ne_zero, if_pos rfl, gaussSumAt_unr_mul hχ one_ne_zero, hqw, e1, e2, map_mul, map_mul,
      hx1, hgG, map_pow σ, map_natCast σ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end GlobalTheory.TameTwistEps
