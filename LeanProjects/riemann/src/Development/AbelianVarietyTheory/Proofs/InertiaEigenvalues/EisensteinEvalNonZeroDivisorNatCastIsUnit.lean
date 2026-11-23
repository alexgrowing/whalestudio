import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem ED_nzd_and_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e),
    (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ
  refine ⟨fun y hy => ?_, fun n hn => ?_⟩
  · have hd : ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
      rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
      exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
    set d := GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))
    have hinj : Function.Injective (LinearMap.mulLeft ℤ_[l] d) := by
      intro x z hxz
      rw [← sub_eq_zero]
      apply GlobalTheory.BKReal.HatDescent.aDp_ev_eis_mul_eq_zero (a := a) ϖ
      simp only [LinearMap.mulLeft_apply] at hxz
      rw [mul_sub, hxz, sub_self]
    have hT := Module.Flat.lTensor_preserves_injective_linearMap (M := O) _ hinj
    have hmul : ∀ z : OD l O, (LinearMap.mulLeft ℤ_[l] d).lTensor O z = ((1 : O) ⊗ₜ[ℤ_[l]] d) * z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul o β => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add x w hx hw => rw [map_add, hx, hw, mul_add]
    apply hT
    rw [hmul, map_zero, ← hd, hy]
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l (Fact.out : l.Prime).one_lt.ne'
    have hmu : IsUnit (m : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
    have hmu' : IsUnit (m : OD l O) := by
      simpa only [map_natCast] using hmu.map (algebraMap ℤ_[l] (OD l O))
    rw [Nat.cast_mul, Nat.cast_pow]
    exact (isUnit_l_OD.pow k).mul hmu'

end GlobalTheory.GalStep
