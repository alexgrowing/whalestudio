import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.JSW.WhitNorm

theorem continuous_whit_and_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  intro E _ _ _ a F hF hl
  refine ⟨?_, fun u hu g => ?_⟩
  · have e : GlobalTheory.JSW.whit F = GroundTheory.Automorphic.FourierWhittaker.partialCoeff F 0 :=
      funext fun g => GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hF g
    rw [e]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hF 0
  · have hu' : u ∈ GlobalTheory.JSW.NA E a := (GlobalTheory.SmGL.mem_unipB _).1 hu
    rw [GlobalTheory.JSW.WhitModel.whit_mul hF hl hu' g, norm_mul, GlobalTheory.JSW.psiN, Circle.norm_coe, one_mul]

end GlobalTheory.JSW.WhitNorm
