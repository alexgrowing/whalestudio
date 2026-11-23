import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
open GlobalTheory.CompanionTheory.Ar.Num

theorem PositivityTheory.Xgn.t_testpt_exists : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (A : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsDiscreteValuationRing A → IsFractionRing A Ω → ¬ IsUnit (p : A) → ∃ (C : Type) (_ : Field C) (_ : Algebra o C) (_ : Algebra Ω C) (_ : IsScalarTower o Ω C) (RC : Subalgebra o C), IsTestPt p A RC ∧ ∀ a : Ω, algebraMap Ω C a ∈ RC → a ∈ A := by
  intro o Ω _ _ _ A p _ hp0 _ _ hu
  have hpA : algebraMap A Ω (p : A) = (p : Ω) := map_natCast _ p
  have ha0 : (p : A) ≠ 0 := fun h => hp0 (by rw [← hpA, h, map_zero])
  obtain ⟨C, _, _, _, _, _, hC, hr⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing A Ω ha0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) (r := 1 / 2) (by norm_num) (by norm_num)
  have hmem : ∀ a : Ω, ‖algebraMap Ω C a‖ ≤ 1 ↔ a ∈ A := fun a => by
    rw [hC]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have hp1 : ‖(p : C)‖ < 1 := by
    rw [hpA, map_natCast] at hr
    rw [hr]; norm_num
  letI : Algebra o C := ((algebraMap Ω C).comp (algebraMap o Ω)).toAlgebra
  haveI : IsScalarTower o Ω C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let RC : Subalgebra o C :=
    { (GlobalTheory.normIntegers C).toSubring.toSubsemiring with
      algebraMap_mem' := fun r =>
        GlobalTheory.mem_normIntegers_iff.2 ((hmem _).2 (A.algebraMap_mem r)) }
  have hRC : ∀ c : C, c ∈ RC ↔ ‖c‖ ≤ 1 := fun c => GlobalTheory.mem_normIntegers_iff
  have hv : ∀ c : C, c ∈ RC ↔ NormedField.valuation c ≤ 1 := fun c => Iff.rfl
  have hO : (NormedField.valuation (K := C)).Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv r).2 hr⟩, rfl⟩⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, RC,
    ⟨inferInstance, ⟨NormedField.valuation, hv, ?_⟩, ?_, fun a ha => (hRC _).2 ((hmem a).2 ha)⟩,
    fun a ha => (hmem a).1 ((hRC _).1 ha)⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe]
    exact hp1
  · refine GlobalTheory.NormIntegers.isAdicComplete_span_singleton hO ?_
    rw [map_natCast]
    exact hp1
