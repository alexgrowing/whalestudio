import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferencesSpanIntertwiners
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differences_span_intertwiners : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ c : ℂ, Diffs B G X om om' R Rf c ≤ Submodule.span ℂ {f | ∃ T : Rf.Pi B.v₁ →ₗ[ℂ] (UA σ G.W.J → ℂ),
      (∀ ξ, T ξ ∈ Diffs B G X om om' R Rf c) ∧
      (∀ y ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, y)) φ φ₁ → ∀ h, T (Rf.p' B.v₁ φ₁) h = T (Rf.p' B.v₁ φ) (h * y)) ∧ ∃ ξ, f = T ξ} := by
  first | exact @GlobalTheory.ThK.DiffsMaps.diffs_le_span_maps | exact GlobalTheory.ThK.DiffsMaps.diffs_le_span_maps | (intros; apply GlobalTheory.ThK.DiffsMaps.diffs_le_span_maps <;> assumption)
