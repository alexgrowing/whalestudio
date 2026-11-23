import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundamentalDomainSmulIff

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

theorem fundamentalDomain_covol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K : Subgroup (HA (AF F) σ J), IsClosed (K : Set (HA (AF F) σ J)) → ∀ μ : Measure K, μ.IsHaarMeasure → (∃ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) ∧ (∀ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ → covol μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧ ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ ratOf (K := K), ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧ ∀ c : NNReal, c ≠ 0 → covol (c • μ) = (c : ℝ) * covol μ := by
  intro F E _ _ _ _ _ σ _ n J _ K _ μ hμ

  refine domains_and_covolume F E σ n J K (ratOf (K := K)) rfl covol ?_ μ hμ
  intro ν hν
  refine ⟨hν.choose, hν.choose_spec, ?_⟩
  rw [covol, dif_pos hν]

end GlobalTheory.ClosedSubgroupCovol
