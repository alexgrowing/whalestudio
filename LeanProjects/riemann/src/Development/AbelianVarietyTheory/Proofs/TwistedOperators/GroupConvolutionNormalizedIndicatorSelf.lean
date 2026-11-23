import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section
namespace GlobalTheory.TrIdem

theorem conv_normInd_self (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G)) :
    conv μ (normInd μ (H : Set G)) (normInd μ (H : Set G)) = normInd μ (H : Set G) := by
  have hm : MeasurableSet (H : Set G) := hHo.measurableSet
  have hpos : μ (H : Set G) ≠ 0 := (hHo.measure_pos μ ⟨1, H.one_mem⟩).ne'
  have hfin : μ (H : Set G) ≠ ⊤ := hHc.measure_lt_top.ne
  have hr : (μ.real (H : Set G) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact (ENNReal.toReal_pos hpos hfin).ne'
  funext y
  simp only [conv, normInd]
  set c : ℂ := (μ.real (H : Set G) : ℂ)⁻¹ with hc
  by_cases hy : y ∈ H
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = (H : Set G).indicator (fun _ => c * c) := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∈ H := H.mul_mem (H.inv_mem hx) hy
        simp [Set.indicator_of_mem (show x ∈ (H : Set G) from hx),
          Set.indicator_of_mem (show x⁻¹ * y ∈ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_indicator_const _ hm]
    simp only [Pi.smul_apply, Set.indicator_of_mem (show y ∈ (H : Set G) from hy), Pi.one_apply, smul_eq_mul, mul_one]
    rw [Complex.real_smul, hc]
    field_simp
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = fun _ => 0 := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∉ H := fun h => hy (by simpa using H.mul_mem hx h)
        simp [Set.indicator_of_notMem (show x⁻¹ * y ∉ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_zero]
    simp [Set.indicator_of_notMem (show y ∉ (H : Set G) from hy)]

end GlobalTheory.TrIdem
