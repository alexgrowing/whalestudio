import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendFreeTupleGramHermitianFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_free_tuple_gram_hermitian_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ f : Fin r → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (Fin.append y f) = (gramE σ J (tupH P)).map (inclR (Fv F v)) := by
  first | exact @GlobalTheory.FrameExtend.extend_frame | exact GlobalTheory.FrameExtend.extend_frame | (intros; apply GlobalTheory.FrameExtend.extend_frame <;> assumption)
