import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataLocalExpansion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_data_local_expansion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∃ (m : ℕ) (φ : Fin m → (Fin a × Fin (a + a') → Fv F B.v₁) → ℂ)
      (L : Fin m → ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ)),
      (∀ j, φ j ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁)) ∧ (∀ j, augAt om B.v₁ ≤ LinearMap.ker (L j)) ∧
      (∀ j, ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ ψ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁),
        ∀ ψ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (1, h)) ψ ψ₁ →
          ∀ y, L j ψ₁ y = L j ψ (y * h)) ∧
      G.M.I om Φ = ∑ j, L j (φ j) := by
  first | exact @GlobalTheory.ThKGlobLoc.exists_sum_local | exact GlobalTheory.ThKGlobLoc.exists_sum_local | (intros; apply GlobalTheory.ThKGlobLoc.exists_sum_local <;> assumption)
