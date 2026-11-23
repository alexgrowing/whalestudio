import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordInverse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_coord_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∀ u ∈ unip σ Y H, coA σ Y.J H u⁻¹ = -coA σ Y.J H u ∧ coC σ Y.J H u⁻¹ = -cA σ (coC σ Y.J H u) := by
  first | exact @GlobalTheory.ThK.UnipDom.PlaneInv.coA_coC_inv | exact GlobalTheory.ThK.UnipDom.PlaneInv.coA_coC_inv | (intros; apply GlobalTheory.ThK.UnipDom.PlaneInv.coA_coC_inv <;> assumption)
