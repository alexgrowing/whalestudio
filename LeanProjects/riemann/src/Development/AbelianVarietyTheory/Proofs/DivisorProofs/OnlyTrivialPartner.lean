import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblOpOfConst

noncomputable section

namespace GlobalTheory.ThK.SmallTheta

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def OnlyTrivialPartner : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ v : Pl F, X.Good v →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (ρ : UA σ G.V'.J → Module.End ℂ Y),
      ρ 1 = 1 → (∀ k ∈ UAt σ G.V' (evFin F v), ∀ k' ∈ UAt σ G.V' (evFin F v), ρ (k * k') = ρ k * ρ k') →
      (∀ y : Y, ∃ U ∈ 𝓝 (1 : UA σ G.V'.J), ∀ k ∈ U, k ∈ UAt σ G.V' (evFin F v) → ρ k y = y) →
      Nontrivial Y → (∀ N : Submodule ℂ Y, (∀ k ∈ UAt σ G.V' (evFin F v), ∀ y ∈ N, ρ k y ∈ N) → N = ⊥ ∨ N = ⊤) →
      ∀ A : UA σ G.W.J → Module.End ℂ (Rf.Pi v),
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ →
        A h (Rf.p' v φ) = Rf.p' v φ₁) →
      ∀ T : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] Y ⊗[ℂ] Rf.Pi v,
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ →
        T φ₁ = TensorProduct.map LinearMap.id (A h) (T φ)) →
      (∀ k ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (k, 1)) φ φ₁ →
        T φ₁ = TensorProduct.map (ρ k) LinearMap.id (T φ)) →
      (∃ φ ∈ SB _, T φ ≠ 0) →
      ∀ k ∈ UAt σ G.V' (evFin F v), ρ k = 1

end GlobalTheory.ThK.SmallTheta

end
