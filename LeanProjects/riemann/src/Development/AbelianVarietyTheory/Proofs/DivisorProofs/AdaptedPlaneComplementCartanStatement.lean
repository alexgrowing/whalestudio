import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementCartan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_complement_cartan : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ P : Matrix (Fin n₁) (Fin n) E, P * H.ι = 1 → ∀ w, IsCartan (Complex.I • W₁.J.map (B.emb w).1) (W₁.θ w) := by
  first | exact @GlobalTheory.SkewPlane.cartan_compl | exact GlobalTheory.SkewPlane.cartan_compl | (intros; apply GlobalTheory.SkewPlane.cartan_compl <;> assumption)
