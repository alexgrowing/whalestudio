import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedDataTensorDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_data_tensor_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a')))
      (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ i, f i ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = G.M'.vac v) ∧
        φ i B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  first | exact @GlobalTheory.ThK.SoPolSplit.exists_sum_pure_pol_so | exact GlobalTheory.ThK.SoPolSplit.exists_sum_pure_pol_so | (intros; apply GlobalTheory.ThK.SoPolSplit.exists_sum_pure_pol_so <;> assumption)
