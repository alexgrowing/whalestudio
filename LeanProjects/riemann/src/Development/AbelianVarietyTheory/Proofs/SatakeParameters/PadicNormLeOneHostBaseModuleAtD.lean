import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.IntegralAtPlace

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := ℂ_[p])).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  intro D p hpF hpd φ a ha
  obtain ⟨-, -, hqd, -, hd2⟩ := hypOdd_of_hostHyp D.host.hyp
  have hint : ∀ y : 𝓞 D.host.E, ‖φ (y : D.host.E)‖ ≤ 1 := fun y => by
    have h : IsIntegral ℤ (φ (y : D.host.E)) := by
      obtain ⟨f, hf, hx⟩ := RingOfIntegers.isIntegral_coe y
      refine ⟨f, hf, ?_⟩
      have := congrArg φ hx
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [RingHom.ext_int (φ.comp (algebraMap ℤ D.host.E)) (algebraMap ℤ ℂ_[p])] at this
    exact norm_le_one_of_isIntegral h
  let Q : Ideal (𝓞 D.host.E) :=
    { carrier := {y | ‖φ (y : D.host.E)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        rw [norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint c)) hx }
  have hmem : ∀ y, y ∈ Q ↔ ‖φ (y : D.host.E)‖ < 1 := fun y => Iff.rfl
  haveI hQ : Q.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
    · have h1 := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at h1
    · rw [hmem, show ((x * y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) * y from rfl, map_mul,
        norm_mul] at hxy
      by_contra hc
      push_neg at hc
      rw [hmem, hmem, not_lt, not_lt] at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  have hpQ : (p : 𝓞 D.host.E) ∈ Q := by
    rw [hmem]
    have e : ((p : 𝓞 D.host.E) : D.host.E) = (p : D.host.E) := by simp
    rw [e, map_natCast]
    have : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨z, hz, hden⟩ := GlobalTheory.AAUnitAway.exists_den D Q hpF.out (by rw [hpd]; exact UpperTheory.Small.d_not_mem D.host)
    (by rw [hpd]; exact hqd.symm) hpQ
  have hz1 : ‖φ (z : D.host.E)‖ = 1 := le_antisymm (hint z) (not_lt.1 ((hmem z).not.1 hz))
  obtain ⟨w, hw⟩ := hden a ha
  have := hint w
  rwa [hw, map_mul, norm_mul, hz1, mul_one] at this

end GlobalTheory.IntegralAtPlace
