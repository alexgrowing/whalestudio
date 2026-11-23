import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBSchwartzOperatorIntertwines
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infRel_schwartz_operator_unique_up_to_scalar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ T T' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)), T ≠ 0 →
    GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') T → GlobalTheory.ThK.EvUniqB.InfRel B G.M' G₁.M' H.ι H'.ι (isoB H H') T' →
    ∃ c : ℂ, T' = c • T := by
  first | exact @GlobalTheory.ArchSchB.infRelB_proportional | exact GlobalTheory.ArchSchB.infRelB_proportional | (intros; apply GlobalTheory.ArchSchB.infRelB_proportional <;> assumption)
