import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOneUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CuspOrth

theorem pet_eq_zero_of_ne_of_hasCentChar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary →
    π.HasCentChar ω → π'.HasCentChar ω → CG.mk π ≠ CG.mk π' →
    ∀ φ ∈ π.V, ∀ φ' ∈ π'.V, pet (latticeGL E a) μ φ.1 φ'.1 = 0 := by
  intro E _ _ _ a μ _ π π' ω hω hπ hπ' hne
  exact pet_eq_zero_of_mk_ne μ hω (CuspSub.hasCentral_iff.2 hπ) (CuspSub.hasCentral_iff.2 hπ') hne

end GlobalTheory.CuspOrth
