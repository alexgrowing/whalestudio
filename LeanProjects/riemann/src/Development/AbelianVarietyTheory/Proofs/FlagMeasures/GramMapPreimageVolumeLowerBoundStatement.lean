import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapPreimageVolumeLowerBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMap_preimage_volume_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S0 : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S0 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → ∀ W : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsOpen W → x ∈ W → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ nhds S0, ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ ((gramR (Fv F v) σ J) ⁻¹' (Subtype.val '' S) ∩ W) := by
  first | exact @GlobalTheory.GramPreimageLB.lb_gram_preimage | exact GlobalTheory.GramPreimageLB.lb_gram_preimage | (intros; apply GlobalTheory.GramPreimageLB.lb_gram_preimage <;> assumption)
