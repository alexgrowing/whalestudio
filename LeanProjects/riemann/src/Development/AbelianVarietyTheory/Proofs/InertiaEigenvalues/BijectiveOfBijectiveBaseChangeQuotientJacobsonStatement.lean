import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfBijectiveBaseChangeQuotientJacobson
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_of_bijective_baseChange_quotient_jacobson : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] (P' : Type) [AddCommGroup P'] [Module A P'] [Module.Finite A P'] [Module.Projective A P'] (w : P →ₗ[A] P'), Function.Bijective (w.baseChange (A ⧸ 𝔞)) → Function.Bijective w := by
  first | exact @GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient | exact GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient | (intros; apply GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient <;> assumption)
