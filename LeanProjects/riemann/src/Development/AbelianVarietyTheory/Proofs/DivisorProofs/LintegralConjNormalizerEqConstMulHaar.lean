import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjEqOfTest
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem lintegral_conj_eq_const_mul :
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure N) (b : G), IsClosed (N : Set G) → ν.IsHaarMeasure → (∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) → ∃ κ : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν := by
  intro G _ _ _ _ _ _ _ _ N ν b hN hν h
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let e := GlobalTheory.ResLine.conjNormalEquiv N b h
  haveI : (ν.map e).IsHaarMeasure := e.isHaarMeasure_map ν
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map e) ν
  have he : Measurable e := e.continuous.measurable
  refine ⟨(Measure.haarScalarFactor (ν.map e) ν : ℝ≥0∞), fun g hg => ?_⟩
  have hg' : Measurable fun u : N => g u := hg.comp measurable_subtype_coe
  have h1 := lintegral_map (μ := ν) hg' he
  rw [hc, lintegral_smul_measure] at h1
  exact h1.symm

end GlobalTheory.SphEis
