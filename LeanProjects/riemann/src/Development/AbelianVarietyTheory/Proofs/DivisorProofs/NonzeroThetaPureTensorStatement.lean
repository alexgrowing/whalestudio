import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroThetaPureTensor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_theta_pure_tensor : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → (∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) →
    ∃ f ∈ G.M.Pol B.ψ B.emb, ∃ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in cofinite, φ v = G.M.vac v) ∧ ∃ h, G.M.I om (pure f φ) h ≠ 0 := by
  first | exact @GlobalTheory.ThK.PureNonzero.exists_pure_ne | exact GlobalTheory.ThK.PureNonzero.exists_pure_ne | (intros; apply GlobalTheory.ThK.PureNonzero.exists_pure_ne <;> assumption)
