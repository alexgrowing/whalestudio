import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTupleHaarInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  first | exact @GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | exact GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | (intros; apply GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant <;> assumption)
