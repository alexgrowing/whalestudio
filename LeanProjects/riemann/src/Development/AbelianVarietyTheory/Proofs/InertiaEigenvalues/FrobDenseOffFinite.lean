import Mathlib
import Formalism.ConjugateSelfDual.StatementRest
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.MainNotions.V

namespace GlobalTheory

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.frob_dense_off_finite : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (T : Set (HeightOneSpectrum (𝓞 F))), T.Finite →
    Dense {σ : _root_.Formalism.ConjugateSelfDual.G F Ω | ∃ v : HeightOneSpectrum (𝓞 F), v ∉ T ∧ ∃ A : ValuationSubring Ω,
      _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) σ} := by
  intro F Ω _ _ _ _ _ T hT
  refine (_root_.GlobalTheory.Published.chebotarevDegreeOne'.dense
    (F := F) (Ω := Ω) hT).mono ?_
  rintro σ ⟨v, hv, -, A, hA, hσ⟩
  exact ⟨v, hv, A, hA, hσ⟩

end GlobalTheory
