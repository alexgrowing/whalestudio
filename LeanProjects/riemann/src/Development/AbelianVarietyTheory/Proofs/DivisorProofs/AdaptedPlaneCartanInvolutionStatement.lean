import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneCartanInvolution
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_cartan_involution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ r' s' i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w : InfinitePlace F,
    (∃ L : Matrix (Fin d₁) (Fin d) ℂ, L * H'.ι.map (B.emb w).1 = 1) → IsCartan (Complex.I • W₁.J.map (B.emb w).1) (W₁.θ w) := by
  first | exact @GlobalTheory.CartanRestrict.isCartan_of_isAdapted | exact GlobalTheory.CartanRestrict.isCartan_of_isAdapted | (intros; apply GlobalTheory.CartanRestrict.isCartan_of_isAdapted <;> assumption)
