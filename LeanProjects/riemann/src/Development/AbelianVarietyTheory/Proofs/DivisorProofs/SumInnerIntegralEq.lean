import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvConjTMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSumInnerOfRangeLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmoothStatement

noncomputable section

open MeasureTheory GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem sum_inner_integral_eq {X U ι : Type} [MeasurableSpace X] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] [Fintype ι] (ν : Measure X) (f : X → ℂ) (ρ : X → U →L[ℂ] U) (e : ι → U) (T : U →L[ℂ] U)
    (h : ∀ v, Integrable (fun x => f x • ρ x v) ν ∧ T v = ∫ x, f x • ρ x v ∂ν) :
    ∑ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, f x * ∑ j, ⟪e j, ρ x (e j)⟫_ℂ ∂ν := by
  have h1 : ∀ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, ⟪e j, f x • ρ x (e j)⟫_ℂ ∂ν := fun j => by
    rw [(h (e j)).2, integral_inner (h (e j)).1]
  simp only [h1]
  rw [← integral_finsetSum _ fun j _ => (h (e j)).1.const_inner (e j)]
  simp only [inner_smul_right, Finset.mul_sum]

theorem stTr_of_range_steps (hF : UFin) (hS : RangeShape) (hK : RangeK) (hT : TraceSum) : StTr := by
  intro n ε μ _ U _ _ _ π hπ hirr d
  obtain ⟨L, hL, hmem, -⟩ := hF n ε U π hπ hirr d
  refine ⟨fun g => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π g (stdOrthonormalBasis ℂ L j : U)⟫_ℂ, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)
  · intro φ hφ
    obtain ⟨hop, hr⟩ := hS n ε μ U π hπ d φ hφ
    have := hT U L _ fun u => hmem _ (hr u).1
    rwa [sum_inner_integral_eq μ (fun g => φ (toM g)) (fun g => π g) _ _ hop] at this
  · intro P hP
    obtain ⟨B, hB, hr⟩ := hK n ε U π hπ P
    refine ⟨B, fun v => (hB v).2, ?_⟩
    have := hT U L B fun u => hmem _ fun l => by
      obtain ⟨Q, hQ, hQ'⟩ := hr u l
      exact ⟨Q, hQ.trans hP, hQ'⟩
    rwa [sum_inner_integral_eq (muK ε) (fun k : KG ε => ev (toMK k) P) (fun k : KG ε => π k) _ _ hB] at this

theorem stTr : StTr := stTr_of_range_steps GlobalTheory.T.polyCoeff_vectors_lie_in_finiteDimensional_smooth GlobalTheory.T.shapeIntegratedOperator_ranges_polynomial rangeK GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le

end GlobalTheory.PsCo.Pc3

end
