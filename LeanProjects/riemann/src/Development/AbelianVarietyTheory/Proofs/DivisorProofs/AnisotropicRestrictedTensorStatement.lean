import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicRestrictedTensor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_restricted_tensor : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ φ' : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M'.Pol B.ψ B.emb →
      (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ' B.v₁ ∈ SB _ → (∀ v, v ≠ B.v₁ → φ' v = φ v) →
      φ B.v₁ - φ' B.v₁ ∈ augAt om' B.v₁ → G.M'.I om' (pure f φ') = G.M'.I om' (pure f φ) := by
  first | exact @GlobalTheory.ThKKill.kill | exact GlobalTheory.ThKKill.kill | (intros; apply GlobalTheory.ThKKill.kill <;> assumption)
