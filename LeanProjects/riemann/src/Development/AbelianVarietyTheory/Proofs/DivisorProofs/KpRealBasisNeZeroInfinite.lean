import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactZeroInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple

noncomputable section

namespace GlobalTheory.ThK.RealB.NeZero

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.EvZeroInf

section Slice

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def pt (x₀ : κ → Af F) (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (x₀ i)

end Slice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ThK.RealB.NeZero
