import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulLocalWittFreeTupleGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_localWitt_free_tuple_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  first | exact @GlobalTheory.LocalWittFree.exists_smul_ratTup_eq | exact GlobalTheory.LocalWittFree.exists_smul_ratTup_eq | (intros; apply GlobalTheory.LocalWittFree.exists_smul_ratTup_eq <;> assumption)
