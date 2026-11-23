import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory

theorem cuspSub_zero_V_eq_top {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (π : CuspSub E 0) :
    π.V = ⊤ := by
  have hsub : Subsingleton (GA E 0) := inferInstance
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  have h1 : (φ : GA E 0 → ℂ) 1 ≠ 0 := by
    intro h
    apply hφ0
    ext g
    rw [Subsingleton.elim g 1]
    simpa using h
  rw [eq_top_iff]
  intro ψ _
  have e : ψ = ((ψ : GA E 0 → ℂ) 1 / (φ : GA E 0 → ℂ) 1) • φ := by
    ext g
    rw [Subsingleton.elim g 1]
    simp [div_mul_cancel₀ _ h1]
  rw [e]
  exact π.V.smul_mem _ hφ

theorem cuspSub_zero_V_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (π π' : CuspSub E 0), π.V = π'.V := by
  intro E _ _ _ π π'
  rw [cuspSub_zero_V_eq_top π, cuspSub_zero_V_eq_top π']

end GlobalTheory
