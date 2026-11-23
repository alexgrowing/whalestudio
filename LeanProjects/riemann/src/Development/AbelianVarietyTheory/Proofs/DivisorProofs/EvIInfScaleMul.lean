import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusTheta

variable (F : Type) [Field F] [NumberField F]

def infScale (s : ℝ) : AF F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) s), 1)

theorem infScale_mul_fst (s : ℝ) (x : AF F) : (infScale F s * x).1 = (infScale F s).1 * x.1 := rfl

theorem infScale_mul_snd (s : ℝ) (x : AF F) : (infScale F s * x).2 = x.2 := by
  show (infScale F s).2 * x.2 = x.2
  simp [infScale]

theorem evI_infScale_mul (s : ℝ) (x : AF F) : evI F (infScale F s * x) = s • evI F x := by
  unfold evI
  rw [infScale_mul_fst, map_mul]
  simp [infScale, Algebra.smul_def]

end GlobalTheory.TorusTheta
