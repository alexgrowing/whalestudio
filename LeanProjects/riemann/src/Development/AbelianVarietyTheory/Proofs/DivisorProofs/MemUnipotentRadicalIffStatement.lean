import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnipotentRadicalIff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unipotent_radical_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (X : Spc F E n) (H : Plane E n n₁) (u : UA σ X.J), u ∈ unip σ X H ↔
      (mat u *ᵥ incV F H.x = incV F H.x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) := by
  first | exact @GlobalTheory.UnipSet.mem_unip_iff | exact GlobalTheory.UnipSet.mem_unip_iff | (intros; apply GlobalTheory.UnipSet.mem_unip_iff <;> assumption)
