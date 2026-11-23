import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeATripleStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_a_triple_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (k : UA σ G.V.J), k ∈ UAt σ G.V (evFin F v) → ∀ l : (AE F E)ˣ,
      mat k *ᵥ incV F H.x = (l : AE F E) • incV F H.x → ∃ g₁ ∈ UAt σ G₁.V (evFin F v), (∀ z : Fin b → AE F E, ∃ a : AE F E, mat k *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g₁ *ᵥ z) + a • incV F H.x) := by
  first | exact @GlobalTheory.LeviQuot.levi_quot | exact GlobalTheory.LeviQuot.levi_quot | (intros; apply GlobalTheory.LeviQuot.levi_quot <;> assumption)
