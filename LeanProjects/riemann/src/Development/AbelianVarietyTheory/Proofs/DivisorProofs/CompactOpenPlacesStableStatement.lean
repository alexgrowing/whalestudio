import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenPlacesStable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_open_places_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ S₀ : Finset (Pl F), ∀ (S T : Finset (Pl F)) (k : UA σ G.W.J), S₀ ⊆ S → T ⊆ S →
      (∀ u : AF F, At (evI F) u → u • (mat k - 1) = 0) →
      (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat k - 1) = 0) →
      (∀ w, w ∉ S → ∀ γ, (γ * Matrix.transpose (mat k) ∈ latAtV G.V G.W w ↔ γ ∈ latAtV G.V G.W w)) →
      (∀ w, w ∉ S → ∀ γ, (γ * Matrix.transpose (mat k) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) →
      (∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ),
        (∀ w, φ w ∈ SB (Fin a × Fin (a + a') → Fv F w)) → (∀ w ∉ T, φ w = G.M.vac w) →
        om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∧
      (∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
        (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w ∉ T, φ w = G.M'.vac w) →
        om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  first | exact @GlobalTheory.TruncFix.fix_off_bad | exact GlobalTheory.TruncFix.fix_off_bad | (intros; apply GlobalTheory.TruncFix.fix_off_bad <;> assumption)
