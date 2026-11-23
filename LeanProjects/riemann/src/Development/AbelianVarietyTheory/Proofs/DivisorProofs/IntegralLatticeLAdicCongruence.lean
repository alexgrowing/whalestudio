import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneModelRestrictionCompatible
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section
open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolD
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_mul_right {n d d₁ : ℕ} {u : Matrix (Fin n) (Fin d₁) (AE F E)} (hu : At (evI F) u)
    (A : Matrix (Fin d₁) (Fin d) (AE F E)) : At (evI F) (u * A) := by
  intro c hc
  rw [← Matrix.smul_mul, hu c hc, Matrix.zero_mul]

end GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.PolD
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.PolD
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.ThK.EvAt0.PolD
