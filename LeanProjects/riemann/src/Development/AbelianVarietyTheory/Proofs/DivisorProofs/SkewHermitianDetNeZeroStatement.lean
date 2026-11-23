import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  first | exact @GlobalTheory.ThK.SkewGram.gram_det_ne_zero | exact GlobalTheory.ThK.SkewGram.gram_det_ne_zero | (intros; apply GlobalTheory.ThK.SkewGram.gram_det_ne_zero <;> assumption)
