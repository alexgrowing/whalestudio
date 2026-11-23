import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryIffGroupPoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_iff_group_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (c : E) (hc : c ≠ 0),
      ∀ g : UA σ J, g ∈ ratU σ J ↔ toGAd hσ J hc g ∈ GlobalTheory.AdelicU.ratPts σ (c • J.map σ) := by
  first | exact @GlobalTheory.RatCorr.ratU_iff_ratPts | exact GlobalTheory.RatCorr.ratU_iff_ratPts | (intros; apply GlobalTheory.RatCorr.ratU_iff_ratPts <;> assumption)
