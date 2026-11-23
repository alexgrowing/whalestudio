import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissibleForm_adelicThetaSum : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ], ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  first | exact @GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | exact GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | (intros; apply GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact <;> assumption)
