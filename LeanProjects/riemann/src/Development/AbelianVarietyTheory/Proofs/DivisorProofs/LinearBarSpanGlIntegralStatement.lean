import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarSpanGlIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_span_gl_integral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι →
    ∀ x ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁),
      (∀ [MeasurableSpace (GL (Fin a') (Fv F B.v₁))] [BorelSpace (GL (Fin a') (Fv F B.v₁))] (μ : Measure (GL (Fin a') (Fv F B.v₁))) [μ.IsHaarMeasure], ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁), Y.rank = a' →
        ∫ g, GlobalTheory.SplitFlip.omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι x) Y ∂μ = 0) →
      x ∈ Submodule.span ℂ {y | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ ψ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ ψ' ∈ G.M'.SoLoc B.ψ B.τ₁,
        Acts (evFin F B.v₁) (om' (g, 1)) ψ ψ' ∧ y = ψ' - ψ} := by
  first | exact @GlobalTheory.TranslationGLHaar.ker_fibre_mem_span | exact GlobalTheory.TranslationGLHaar.ker_fibre_mem_span | (intros; apply GlobalTheory.TranslationGLHaar.ker_fibre_mem_span <;> assumption)
