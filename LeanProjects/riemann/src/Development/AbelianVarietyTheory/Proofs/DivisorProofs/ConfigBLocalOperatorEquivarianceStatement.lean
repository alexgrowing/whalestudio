import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalOperatorEquivariance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_local_operator_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (T T' : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    GlobalTheory.ThK.EvUniqB.FinRel B G.M' G₁.M' H.ι H'.ι (isoB H H') v T → GlobalTheory.ThK.EvUniqB.FinRel B G.M' G₁.M' H.ι H'.ι (isoB H H') v T' →
    (SB _).map T = SB _ → (SB _).map T' = SB _ → T (G.M'.vac v) = G₁.M'.vac v → T' (G.M'.vac v) = G₁.M'.vac v →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), T' φ = T φ := by
  first | exact @GlobalTheory.ThK.EvUniqB.finRel_unique | exact GlobalTheory.ThK.EvUniqB.finRel_unique | (intros; apply GlobalTheory.ThK.EvUniqB.finRel_unique <;> assumption)
