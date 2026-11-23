import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem exists_isInfFam_family : ∀ D : D7, ∃ θ : InfFam D, IsInfFam θ :=
  fun D => GlobalTheory.DualPairCompare.exists_infFam D

end GlobalTheory.Member
