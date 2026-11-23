import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinAlg

open Polynomial

theorem finiteDimensional_of_roots_of_eigenspaces {M : Type} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) (s : Multiset ℂ) :
    ∀ V : Submodule ℂ M, (∀ v ∈ V, T v ∈ V) →
      (∀ v ∈ V, aeval T ((s.map fun a => (X - C a : ℂ[X])).prod) v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  induction s using Multiset.induction_on with
  | empty =>
    intro V _ hker _
    have hbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℂ).mpr (by simpa using hker v hv)
    subst hbot
    infer_instance
  | cons a s ih =>
    intro V hV hker hfin
    set f : Module.End ℂ M := aeval T (X - C a : ℂ[X]) with hf
    have hfv : ∀ v, f v = T v - a • v := by
      intro v
      simp [f]
    have hWV : ∀ w ∈ V.map f, w ∈ V := by
      rintro w ⟨v, hv, rfl⟩
      rw [hfv]
      exact V.sub_mem (hV v hv) (V.smul_mem a hv)
    have hW1 : ∀ w ∈ V.map f, T w ∈ V.map f := by
      rintro w ⟨v, hv, rfl⟩
      refine ⟨T v, hV v hv, ?_⟩
      simp [hfv, map_sub, map_smul]
    have hW2 : ∀ w ∈ V.map f,
        aeval T ((s.map fun b => (X - C b : ℂ[X])).prod) w = 0 := by
      rintro w ⟨v, hv, rfl⟩
      have h := hker v hv
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, map_mul] at h
      exact h
    have hW3 : ∀ c : ℂ, FiniteDimensional ℂ
        (Submodule.span ℂ {v | v ∈ V.map f ∧ T v = c • v}) := by
      intro c
      haveI := hfin c
      have hsub : {v | v ∈ V.map f ∧ T v = c • v} ⊆ {v | v ∈ V ∧ T v = c • v} :=
        fun v hv => ⟨hWV v hv.1, hv.2⟩
      exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)
    have hWfin : FiniteDimensional ℂ (V.map f) := ih (V.map f) hW1 hW2 hW3
    apply Module.Finite.iff_fg.mpr
    apply Submodule.fg_of_fg_map_of_fg_inf_ker f
    · exact Module.Finite.iff_fg.mp hWfin
    · haveI := hfin a
      have hle : V ⊓ LinearMap.ker f ≤ Submodule.span ℂ {v | v ∈ V ∧ T v = a • v} := by
        rintro v ⟨hv, hk⟩
        apply Submodule.subset_span
        refine ⟨hv, ?_⟩
        have h0 : f v = 0 := hk
        rw [hfv, sub_eq_zero] at h0
        exact h0
      haveI := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.iff_fg.mp inferInstance

theorem finiteDimensional_of_polynomial_of_eigenspaces :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M),
      (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 →
      (∀ v ∈ V, Polynomial.aeval T p v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  intro M _ _ T V hV p hp hker hfin
  have hsplit : p = C p.leadingCoeff * (p.roots.map fun a => (X - C a : ℂ[X])).prod := by
    first
      | exact Polynomial.eq_prod_roots_of_splits_id (IsAlgClosed.splits p)
      | exact (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))).symm
  refine finiteDimensional_of_roots_of_eigenspaces T p.roots V hV ?_ hfin
  intro v hv
  have h := hker v hv
  rw [hsplit, map_mul, Polynomial.aeval_C] at h
  have h' : p.leadingCoeff • aeval T ((p.roots.map fun a => (X - C a : ℂ[X])).prod) v = 0 := by
    rw [← h, Algebra.algebraMap_eq_smul_one]
    rfl
  exact (smul_eq_zero.mp h').resolve_left (Polynomial.leadingCoeff_ne_zero.mpr hp)

end GlobalTheory.CompanionTheory.LinAlg
