import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : Type) [Fintype ι] (b : Module.Basis ι F E) (d : ℕ)
    (μ : @Measure (Fin d → AE F E) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ ν : @Measure (Fin d × ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν ∧
      ∀ g : (Fin d × ι → AF F) → ℂ,
        (Integrable g ν → Integrable (fun u : Fin d → AE F E => g (fun p => (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2)) μ) ∧
        ∫ u, g (fun p => (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2) ∂μ = ∫ t, g t ∂ν := by
  first | exact @GlobalTheory.HaarCoord.haar_coord_transfer | exact GlobalTheory.HaarCoord.haar_coord_transfer | (intros; apply GlobalTheory.HaarCoord.haar_coord_transfer <;> assumption)
