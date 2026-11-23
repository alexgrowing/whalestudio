import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSplitBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_complement_split_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) W₁.L (W₁.bas v) := by
  first | exact @GlobalTheory.AdaptedPlaneBasis.isSplitBasis_of_isAdapted | exact GlobalTheory.AdaptedPlaneBasis.isSplitBasis_of_isAdapted | (intros; apply GlobalTheory.AdaptedPlaneBasis.isSplitBasis_of_isAdapted <;> assumption)
