import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCoordSurj
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotent_coord_surj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∀ α : Fin n₁ → E, ∃ γ ∈ unip σ Y H, γ ∈ ratU σ Y.J ∧ coA σ Y.J H γ = fun j => inclR (F := F) (AF F) (α j) := by
  first | exact @GlobalTheory.ThK.UnipRat.exists_rat_unip_coA | exact GlobalTheory.ThK.UnipRat.exists_rat_unip_coA | (intros; apply GlobalTheory.ThK.UnipRat.exists_rat_unip_coA <;> assumption)
