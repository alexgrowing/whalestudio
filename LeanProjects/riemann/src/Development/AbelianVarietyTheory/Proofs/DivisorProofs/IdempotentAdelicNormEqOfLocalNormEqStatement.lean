import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEq
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E, (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.NormFin.idem_norm_eq_of_local | exact GlobalTheory.NormFin.idem_norm_eq_of_local | (intros; apply GlobalTheory.NormFin.idem_norm_eq_of_local <;> assumption)
