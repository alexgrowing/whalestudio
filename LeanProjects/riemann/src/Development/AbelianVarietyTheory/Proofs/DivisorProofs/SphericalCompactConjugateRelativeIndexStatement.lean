import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCompactConjugateRelativeIndex
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_compact_conjugate_relative_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (v : Pl F) (g : GlobalTheory.SphLine.locU σ G.W v),
      (((GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v)).map (MulAut.conj g).toMonoidHom).relIndex
        ((GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v)) ≠ 0 := by
  first | exact @GlobalTheory.SphLineComm.commensurated | exact GlobalTheory.SphLineComm.commensurated | (intros; apply GlobalTheory.SphLineComm.commensurated <;> assumption)
