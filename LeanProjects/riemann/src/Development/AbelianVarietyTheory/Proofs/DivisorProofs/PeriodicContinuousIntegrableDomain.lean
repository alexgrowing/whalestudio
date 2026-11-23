import Mathlib
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

theorem integrableOn_fundamentalDomain_of_periodic :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (F : (Fin g → ℂ) → ℝ)
      (Fd : Set (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Continuous F →
      (∀ (l : Λ) z, F (z + l) = F z) → IsAddFundamentalDomain Λ Fd volume →
      IntegrableOn F Fd volume := by
  intro g Λ _ F Fd hspan hF hper hFd
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  haveI : MeasurableVAdd Λ (Fin g → ℂ) :=
    (inferInstance : MeasurableVAdd Λ.toAddSubgroup (Fin g → ℂ))
  haveI : VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
    (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup (Fin g → ℂ) volume)
  let b := Module.Free.chooseBasis ℤ Λ
  have hP := ZLattice.isAddFundamentalDomain b (volume : Measure (Fin g → ℂ))
  have hinv : ∀ (l : Λ) (x : Fin g → ℂ), F (l +ᵥ x) = F x := by
    intro l x
    rw [Submodule.vadd_def, vadd_eq_add, add_comm]
    exact hper l x
  rw [hFd.integrableOn_iff hP hinv]
  have hbdd := ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ))) :=
    hbdd.isCompact_closure
  exact (hF.continuousOn.integrableOn_compact hcpt).mono_set subset_closure

end GlobalTheory
