import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductDecayVacuum
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_decay_vacuum : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  first | exact @GlobalTheory.SoPureThetaCont.continuous_I_pure | exact GlobalTheory.SoPureThetaCont.continuous_I_pure | (intros; apply GlobalTheory.SoPureThetaCont.continuous_I_pure <;> assumption)
