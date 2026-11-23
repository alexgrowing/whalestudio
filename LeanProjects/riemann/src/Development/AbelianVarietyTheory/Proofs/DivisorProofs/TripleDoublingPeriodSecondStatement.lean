import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleDoublingPeriodSecond
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_doubling_period_second : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → G.p = 0 → G.q = 0 →
    ∀ (X₂ : Spc F E (a' + a')) (i : UA σ G.V'.J × UA σ G.V'.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B G.V' X₂ i K₂ →
    ∀ [MeasurableSpace (Fin a' × Fin (a + a') → AF F)] [BorelSpace (Fin a' × Fin (a + a') → AF F)] (m : Measure (Fin a' × Fin (a + a') → AF F)), m.IsAddHaarMeasure →
    ∃ f ∈ G.M'.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → pure f φ ≠ 0 →
      ∀ μ : Measure (UAtSub σ G.V' (evI F)), μ.IsHaarMeasure → ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om' (pure f φ) i K₂ _ μ s = z := by
  first | exact @GlobalTheory.DefiniteRealZeta.real_zeta_small | exact GlobalTheory.DefiniteRealZeta.real_zeta_small | (intros; apply GlobalTheory.DefiniteRealZeta.real_zeta_small <;> assumption)
