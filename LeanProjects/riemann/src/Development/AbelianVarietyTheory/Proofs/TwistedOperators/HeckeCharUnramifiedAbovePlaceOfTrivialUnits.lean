import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOverPlace

theorem unrAt_of_unramAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F),
    IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  intro D χ v ε hε hu w hw x hx
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w x).1 hx
  have hc := GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E)
  obtain ⟨k0, k1, -⟩ := GlobalTheory.CMPrimeIdele.place_comp hc hε
  have key : χ (GlobalTheory.LFun.locIdele D.host.F w x) = 1 := by
    refine hu _ ?_ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w x).2 h1) (by
      rw [← map_inv]; exact (GlobalTheory.LFun.EulerTie.locIdele_int_iff w x⁻¹).2 h2)
    refine hc.ext' ?_ fun Q ↦ ?_
    · have k0' : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) ε) = 0 := k0
      have k2 : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) = 0 := by
        rw [map_sub, (GlobalTheory.LFun.EulerTie.parts_locIdele w x).1, map_one, sub_self]
      rw [map_mul, k0', zero_mul, k2]
    · rw [GlobalTheory.CMPrimeIdele.ev_mul]
      by_cases hQ : Q = w
      · subst hQ
        rw [k1 Q hw, one_mul]
      · have e : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) Q = 0 := by
          rw [map_sub, map_one]
          show GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (GlobalTheory.LFun.locIdele D.host.F w x : AE D) Q - 1 = 0
          rw [GlobalTheory.LFun.EulerTie.finComp_locIdele_ne hQ, sub_self]
        rw [e, mul_zero]
  show Circle.toUnits (χ (GlobalTheory.LFun.locIdele D.host.F w x)) = 1
  rw [key, map_one]

end GlobalTheory.UnrOverPlace
