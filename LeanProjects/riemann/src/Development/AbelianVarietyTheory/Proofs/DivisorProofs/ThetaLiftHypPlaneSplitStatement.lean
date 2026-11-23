import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftHypPlaneSplit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_hyp_plane_split : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∃ (ν₀ β₀ : (Fv F B.v₁)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁) → ℂ))
      (ℓ : Fin a → Fv F B.v₁) (ψv : AddChar (Fv F B.v₁) ℂ),
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt B.v₁) : ℂ)) ^ m ≠ (r : ℂ)) ∧ ℓ ≠ 0 ∧ Continuous ψv ∧ ψv ≠ 1 ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F B.v₁) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)) : Set _) ∧
      (∀ g' : GL (Fin a) (Fv F B.v₁), ∃ g ∈ UAt σ G.V (evFin F B.v₁), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F B.v₁), ∃ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (1, y)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) ∧
      (∀ z : Fin (a + a') → Fv F B.v₁, ∃ u ∈ {u : Matrix (Fin a) (Fin (a + a')) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z},
        At (evFin F B.v₁) u ∧ ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (G.M.co.rho B.ψ u) φ φ₁ ∧ ι φ₁ = fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * ι φ Y) := by
  first | exact @GlobalTheory.PairingVecMulVec.goodPlace_model | exact GlobalTheory.PairingVecMulVec.goodPlace_model | (intros; apply GlobalTheory.PairingVecMulVec.goodPlace_model <;> assumption)
