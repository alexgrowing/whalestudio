import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory

theorem piTensor_isSubquotient_jac_degZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (jac e π) := by
  intro k _ _ _ _ N hN V _ _ _ π d X _ _ ρ e
  subst hN
  have hK : twKer π (unipRad k e) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro w ⟨n, v, rfl⟩
    have h1 : (n : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
    simp [h1]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hx : (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_bot]; exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Jacquet π (unipRad k e)),
      φ (Submodule.Quotient.mk v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let L : Jacquet π (unipRad k e) →ₗ[ℂ] PiTensorProduct ℂ X :=
    (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.toLinearMap ∘ₗ φ
  refine IsSubquotient.of_surjective ⟨L, fun g => ?_⟩ ?_
  · have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    rw [map_one, map_one]
    rfl
  · have hsurj : Function.Surjective φ := fun c =>
      ⟨(c / φ (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, by simp [hφ]⟩
    exact (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.surjective.comp hsurj

end GlobalTheory
