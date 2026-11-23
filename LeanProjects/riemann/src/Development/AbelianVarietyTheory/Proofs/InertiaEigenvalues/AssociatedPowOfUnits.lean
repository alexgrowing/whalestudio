import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BdRDVR

section General

variable {R : Type*} [CommRing R]

theorem irreducible_of_units [IsDomain R] {x : R} (hx0 : x ≠ 0) (hxu : ¬ IsUnit x)
    (hu : ∀ y : R, ¬ x ∣ y → IsUnit y) : Irreducible x := by
  refine ⟨hxu, fun a b hab => ?_⟩
  by_cases ha : x ∣ a
  · right
    obtain ⟨c, rfl⟩ := ha
    have h1 : x * 1 = x * (c * b) := by rw [mul_one, ← mul_assoc]; exact hab
    have h2 := mul_left_cancel₀ hx0 h1
    exact IsUnit.of_mul_eq_one_right c h2.symm
  · exact Or.inl (hu a ha)

theorem associated_pow_of_units {x : R} (hu : ∀ y : R, ¬ x ∣ y → IsUnit y)
    [IsHausdorff (Ideal.span {x}) R] {y : R} (hy : y ≠ 0) : ∃ n : ℕ, Associated (x ^ n) y := by
  classical
  have hex : ∃ n : ℕ, ¬ x ^ n ∣ y := by
    by_contra h
    push_neg at h
    apply hy
    refine IsHausdorff.haus (I := Ideal.span {x}) inferInstance y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n
  have hN := Nat.find_spec hex
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    exact hN (one_dvd _)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hmin : x ^ m ∣ y := by
    have := Nat.find_min hex (m := m) (by omega)
    exact not_not.1 this
  obtain ⟨c, rfl⟩ := hmin
  have hc : IsUnit c := hu c fun hxc => hN (by
    rw [hm, pow_succ]
    exact mul_dvd_mul_left _ hxc)
  exact ⟨m, hc.unit, rfl⟩

end General

theorem core_dvr (l : ℕ) [Fact l.Prime] (C : Core l) : C.DVR := by
  have he := core_isEps l C
  obtain ⟨hdom, hinj, hfield, hden⟩ := BdRField.bdR_isField l
  obtain ⟨hfil, hreg, hcomp, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, -⟩ := thetaD_props l
  obtain ⟨-, ht1, ht2, -⟩ := core_t_unit_fil l C
  have hden' := hden C.ε he
  clear hden
  generalize aDp l (xi C.ε) = x at hfil hreg hcomp hden'
  have hθ : ∀ y : Per.BdRp l, Per.θD l y = 0 ↔ x ∣ y := fun y => by
    rw [hker, hfil, pow_one]
  have hu : ∀ y : Per.BdRp l, ¬ x ∣ y → IsUnit y := fun y hy => hunit y fun h => hy ((hθ y).1 h)
  have hx0 : x ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hxu : ¬ IsUnit x := fun h => (h.map (Per.θD l)).ne_zero ((hθ x).2 dvd_rfl)
  have hirr : Irreducible x := irreducible_of_units hx0 hxu hu
  haveI : IsHausdorff (Ideal.span {x}) (Per.BdRp l) := hcomp.toIsHausdorff
  haveI hdvr : IsDiscreteValuationRing (Per.BdRp l) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨x, hirr, fun hy => associated_pow_of_units hu hy⟩
  have hmax : IsLocalRing.maximalIdeal (Per.BdRp l) = Ideal.span {x} := hirr.maximalIdeal_eq
  have hassoc : Associated x (C.j C.t) := by
    obtain ⟨c, hc⟩ := (hfil 1 _).1 ht1
    rw [pow_one] at hc
    have hcu : IsUnit c := hu c fun hxc => ht2 ((hfil 2 _).2 (by
      rw [hc, pow_two]
      exact mul_dvd_mul_left _ hxc))
    exact ⟨hcu.unit, hc.symm⟩
  refine ⟨hdom, hdvr, ?_, ?_, ?_, fun n => ?_, ?_⟩
  · rw [hmax]
    exact Ideal.span_singleton_eq_span_singleton.2 hassoc
  · rw [hmax]
    ext y
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, hθ]
  · rw [hmax]
    exact hcomp
  · ext y
    rw [hfil, Ideal.mem_span_singleton]
    exact (hassoc.pow_pow (n := n)).dvd_iff_dvd_left
  · refine (isLocalization_iff _ _).2 ⟨fun y => ?_, fun z => ?_, fun {a b} h => ⟨1, by rw [hinj h]⟩⟩
    · have hy : algebraMap (Per.BdRp l) (Per.BdR l) y ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hy
      exact IsUnit.of_mul_eq_one b hb
    · obtain ⟨n, y, h⟩ := hden' z
      exact ⟨(y, ⟨x ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hx0)⟩), by
        simpa only [map_pow] using h⟩

end GlobalTheory.MemLoc.BdRDVR
