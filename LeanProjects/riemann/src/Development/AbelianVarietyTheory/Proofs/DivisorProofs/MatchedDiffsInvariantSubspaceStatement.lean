import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDiffsInvariantSubspace
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
theorem _root_.GlobalTheory.T.matched_diffs_invariant_subspace : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (c : ℂ) (N : Submodule ℂ (UA σ G.W.J → ℂ)), (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ F₀ ∈ N, (fun h => F₀ (h * y)) ∈ N) →
    ∀ f ∈ GlobalTheory.ThK.DescB.Diffs B G X om om' R Rf c, f ∈ N →
      f ∈ Submodule.span ℂ {F₀ | ∃ T : ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ),
        (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), T φ ∈ N) ∧ augAt om B.v₁ ≤ LinearMap.ker T ∧
        (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om (1, y)) φ φ₁ → ∀ h, T φ₁ h = T φ (h * y)) ∧ ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), F₀ = T φ} := by
  first | exact @GlobalTheory.ThK.TransMaps.diffs_mem_span_maps | exact GlobalTheory.ThK.TransMaps.diffs_mem_span_maps | (intros; apply GlobalTheory.ThK.TransMaps.diffs_mem_span_maps <;> assumption)
