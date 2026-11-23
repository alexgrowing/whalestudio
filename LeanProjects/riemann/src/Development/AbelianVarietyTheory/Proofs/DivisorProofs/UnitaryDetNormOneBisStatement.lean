import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetNormOneBis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_det_norm_one_bis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (V : Spc F E n) (r s : ℕ), V.IsHerm σ B r s → ∀ g : UA σ V.J, (mat g).det * cA σ (mat g).det = 1 := by
  first | exact @GlobalTheory.ThK.LiftConst.det_mul_conj_det_eq_one | exact GlobalTheory.ThK.LiftConst.det_mul_conj_det_eq_one | (intros; apply GlobalTheory.ThK.LiftConst.det_mul_conj_det_eq_one <;> assumption)
