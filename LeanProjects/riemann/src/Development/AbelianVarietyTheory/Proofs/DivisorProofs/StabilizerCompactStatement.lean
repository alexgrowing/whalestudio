import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_compact : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ) (K : Subgroup (UA σ X.J)),
    B.IsGood σ → X.IsHerm σ B r s → IsStab B K → IsCompact (K : Set (UA σ X.J)) := by
  first | exact @GlobalTheory.StabCpt.isCompact_of_isStab | exact GlobalTheory.StabCpt.isCompact_of_isStab | (intros; apply GlobalTheory.StabCpt.isCompact_of_isStab <;> assumption)
