import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoordPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCoordinatesHomeomorph

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem eq_of_test_haar {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {κ P : Measure V} {χ : V → V → ℂ}
    (hκ : SelfDual κ χ) (hP : P.IsAddHaarMeasure) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂P) P) (z : V)
    (h1 : ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P = Φ (-z)) (hz : Φ (-z) ≠ 0) : κ = P := by
  have := hκ.1
  have e : κ = Measure.addHaarScalarFactor κ P • P := Measure.isAddLeftInvariant_eq_smul κ P
  set c : NNReal := Measure.addHaarScalarFactor κ P with hcdef
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂κ = (c : ℂ) * ∫ x, Φ x * χ x y ∂P := by
    intro y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hI' : Integrable (fun y => ∫ x, Φ x * χ x y ∂κ) κ := by
    simp only [hT]
    rw [e]
    exact (hI.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hκ.2 Φ hc hs hI' z
  simp only [hT] at h2
  rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h3 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂P) * χ y z ∂P =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [h3, h1, ← mul_assoc] at h2
  have h4 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ hz (by rw [h2, one_mul])
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [e, h6, one_smul]

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem isHermND_one {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    IsHermND σ (1 : Matrix (Fin 1) (Fin 1) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp

end GlobalTheory.HermSD
