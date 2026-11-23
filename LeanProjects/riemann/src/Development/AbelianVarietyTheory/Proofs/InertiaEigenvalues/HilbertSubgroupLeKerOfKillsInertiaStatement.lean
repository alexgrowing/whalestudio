import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HilbertSubgroupLeKerOfKillsInertia
import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  first | exact @GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | exact GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | (intros; apply GlobalTheory.HilbertKill.hilbertSubgroup_le_ker <;> assumption)
