import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc.FilSeed

variable {l : ℕ} [Fact l.Prime]

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  obtain ⟨-, hone, -, -, -, -, hlast⟩ := filD_laws l
  have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (hlast 0 1).1 (by rw [map_one, Nat.cast_zero]; exact hone)
  simpa using Ideal.mul_mem_left _ y h1

theorem exists_unit (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ c : (Per.BdRp l)ˣ, aDp l ξ = (c : Per.BdRp l) * aDp l (xi C.ε) := by
  have hreg := (filtration_eq_xi_pow l C.ε (core_isEps l C)).2.1
  rw [C.ker_theta] at hξ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hξ ▸ Ideal.mem_span_singleton_self ξ :
    ξ ∈ Ideal.span {xi C.ε})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hξ.symm ▸ Ideal.mem_span_singleton_self (xi C.ε) :
    xi C.ε ∈ Ideal.span {ξ})
  have h1 : aDp l a * aDp l b = 1 := by
    have : aDp l (xi C.ε) * (aDp l a * aDp l b - 1) = 0 := by
      have e : aDp l (xi C.ε) = aDp l b * (aDp l a * aDp l (xi C.ε)) := by
        rw [← map_mul, ← map_mul, ha, hb]
      linear_combination -e
    exact sub_eq_zero.1 (hreg _ this)
  refine ⟨⟨aDp l a, aDp l b, h1, by rw [mul_comm, h1]⟩, ?_⟩
  rw [← ha, map_mul]

end GlobalTheory.MemLoc.FilSeed

open GlobalTheory.MemLoc.FilSeed in

theorem GlobalTheory.MemLoc.seed_fil : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → (∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n}) ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a) ∧ (∀ (n : ℕ) (z : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n ↔ z ∈ Per.FilP l n) ∧ (∀ x : Per.BdR l, ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ))) ∧ (∀ (a : ℤ) (n : ℕ) (x : Per.BdR l), algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ n * x ∈ Per.FilD l (a + n) ↔ x ∈ Per.FilD l a) ∧ Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  intro l _ C ξ hξ
  obtain ⟨hstep, hone, hmul, hex, -, -, hlast⟩ := filD_laws l
  obtain ⟨hP, hreg, -, -⟩ := filtration_eq_xi_pow l C.ε (core_isEps l C)
  obtain ⟨c, hc⟩ := exists_unit C ξ hξ
  have h1 : ∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n} := by
    intro n
    ext y
    rw [hP, Ideal.mem_span_singleton, hc, mul_pow, ← Units.val_pow_eq_pow_val,
      Units.mul_left_dvd]
  have hanti : ∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a := by
    intro a b hab
    induction b, hab using Int.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact (hstep b).trans ih
  refine ⟨h1, hmul, hanti, hlast, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := hex x
    exact ⟨(-a).toNat, hanti _ _ (by omega) ha⟩
  · intro a n x
    set w := algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) with hw
    have hwn : w ^ n ∈ Per.FilD l n := by
      rw [hw, ← map_pow, hlast, h1]
      exact Ideal.mem_span_singleton_self _

    have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hw0 : w ≠ 0 := by
      intro h
      have h0 : aDp l ξ = 0 := hinj (by rw [← hw, h, map_zero])
      rw [hc] at h0
      have h2 : aDp l (xi C.ε) = 0 := (Units.mul_right_eq_zero c).1 h0
      exact one_ne_zero (hreg 1 (by rw [h2, zero_mul]))
    haveI := hfr
    have hne : aDp l ξ ≠ 0 := fun h => hw0 (by rw [hw, h, map_zero])
    obtain ⟨u, hu⟩ : IsUnit w :=
      IsLocalization.map_units (Per.BdR l) (⟨aDp l ξ, mem_nonZeroDivisors_of_ne_zero hne⟩ : nonZeroDivisors _)
    have hv : ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ∈ Per.FilD l (-1) := by
      rw [mem_FilD_iff_xi_pow l C.ε (core_isEps l C)]
      refine ⟨((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l), ?_⟩
      have e1 : (- (-1 : ℤ)).toNat = 1 := by norm_num
      have e2 : (-1 : ℤ).toNat = 0 := by norm_num
      have e3 : aDp l (xi C.ε) = aDp l ξ * ((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) := by
        rw [hc, mul_comm (c : Per.BdRp l), mul_assoc, Units.mul_inv, mul_one]
      rw [e1, e2, pow_one, pow_zero, e3, map_mul (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l ξ), ← hw, ← hu,
        ← mul_assoc, Units.inv_mul, one_mul]
      simp
    have hvn : ∀ k : ℕ, ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ k ∈ Per.FilD l (-(k : ℤ)) := by
      intro k
      induction k with
      | zero => simpa using hone
      | succ k ih =>
        rw [pow_succ]
        have := hmul _ _ _ _ ih hv
        rwa [show -(k : ℤ) + -1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
    constructor
    · intro h
      have := hmul _ _ _ _ (hvn n) h
      rwa [← mul_assoc, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_mul,
        show -(n : ℤ) + (a + n) = a by ring] at this
    · intro h
      have := hmul _ _ _ _ hwn h
      rwa [add_comm] at this
  · have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    haveI := hfr
    have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hplus : Function.Injective C.jP := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).2.2
    have hloc : Function.Injective (algebraMap (Per.Acris l) (BcrisP l)) := by
      refine IsLocalization.injective (M := Submonoid.powers ((l : ℕ) : Per.Acris l)) (BcrisP l) ?_
      rw [Submonoid.powers_le, mem_nonZeroDivisors_iff]
      have ht := (acris_torsionFree_complete l).1
      exact ⟨ht, fun x hx => ht x (by rw [mul_comm]; exact hx)⟩
    intro x y hxy
    apply hloc
    apply hplus
    apply hinjD
    rw [C.jP_alg, C.jP_alg, ← C.ι_j, ← C.ι_j, hxy]
