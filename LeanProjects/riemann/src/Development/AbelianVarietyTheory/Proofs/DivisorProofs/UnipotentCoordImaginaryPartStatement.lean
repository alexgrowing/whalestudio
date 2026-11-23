import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordImaginaryPart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_coord_imaginary_part : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∃ g : (Fin n₁ → AE F E) → AE F E, Continuous g ∧ ∀ u ∈ unip σ Y H, coC σ Y.J H u - cA σ (coC σ Y.J H u) = g (coA σ Y.J H u) := by
  first | exact @GlobalTheory.ThK.UnipDom.coC_sub_conj_plane | exact GlobalTheory.ThK.UnipDom.coC_sub_conj_plane | (intros; apply GlobalTheory.ThK.UnipDom.coC_sub_conj_plane <;> assumption)
