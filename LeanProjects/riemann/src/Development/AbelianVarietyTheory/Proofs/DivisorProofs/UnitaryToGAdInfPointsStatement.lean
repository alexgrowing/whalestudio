import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToGAdInfPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_to_GAd_inf_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (W : Spc F E d) (c : E) (hc : c ≠ 0),
    ∀ g ∈ UAt σ W (evI F), toGAd hσ W.J hc g ∈ infPts σ (c • W.J.map σ) := by
  first | exact @GlobalTheory.ThK.SquareIntegrability.toGAd_mem_infPts_of_uAt | exact GlobalTheory.ThK.SquareIntegrability.toGAd_mem_infPts_of_uAt | (intros; apply GlobalTheory.ThK.SquareIntegrability.toGAd_mem_infPts_of_uAt <;> assumption)
