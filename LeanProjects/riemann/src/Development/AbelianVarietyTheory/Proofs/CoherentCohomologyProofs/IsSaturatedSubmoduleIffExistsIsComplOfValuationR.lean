import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply

open Module

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_isCompl_of_projective_quotient (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ N' : Submodule R M, IsCompl N N' := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' (y : M ⧸ N) : N.mkQ (s y) = y := LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    have hy : y = 0 := by
      rw [← hs' y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (N.mkQ x), ?_, s (N.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]

theorem finite_of_isCompl [Module.Finite R M] {N N' : Submodule R M} (h : IsCompl N N') :
    Module.Finite R N :=
  Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

theorem exists_disjoint_sup_eq_of_isCompl_submoduleOf {P N : Submodule R M} (hle : N ≤ P)
    {Q : Submodule R P} (h : IsCompl (N.submoduleOf P) Q) :
    ∃ N' : Submodule R M, Disjoint N N' ∧ N ⊔ N' = P := by
  have hN : (N.submoduleOf P).map P.subtype = N := by
    rw [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  refine ⟨Q.map P.subtype, ?_, ?_⟩
  · rw [← hN, disjoint_iff, ← Submodule.map_inf _ P.injective_subtype, h.inf_eq_bot,
      Submodule.map_bot]
  · conv_lhs => rw [← hN]
    rw [← Submodule.map_sup, h.sup_eq_top, Submodule.map_top, Submodule.range_subtype]

end General

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {M : Type*} [AddCommGroup M] [Module R M]

variable (R M) in

theorem projective_of_finite_of_isTorsionFree [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Projective R M :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation

theorem IsSaturatedSubmodule.projective_quotient [Module.Finite R M] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : Module.Projective R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  projective_of_finite_of_isTorsionFree R (M ⧸ N)

theorem IsSaturatedSubmodule.exists_isCompl [Module.Finite R M] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.projective_quotient
  exists_isCompl_of_projective_quotient N

theorem IsSaturatedIn.exists_disjoint_sup_eq {P N : Submodule R M} [Module.Finite R P]
    (h : IsSaturatedIn P N) : ∃ N' : Submodule R M, Disjoint N N' ∧ N ⊔ N' = P := by
  obtain ⟨Q, hQ⟩ := (isSaturatedIn_iff.1 h).2.exists_isCompl
  exact exists_disjoint_sup_eq_of_isCompl_submoduleOf h.le hQ

end Dedekind

section PID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

end PID

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

variable (R M) in

theorem free_of_finite_of_isTorsionFree_of_valuationRing [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  haveI : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)
  Module.free_of_flat_of_isLocalRing

theorem IsSaturatedSubmodule.free_quotient_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  free_of_finite_of_isTorsionFree_of_valuationRing R (M ⧸ N)

theorem IsSaturatedSubmodule.exists_isCompl_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.free_quotient_of_valuationRing
  exists_isCompl_of_projective_quotient N

theorem IsSaturatedSubmodule.finite_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Finite R N :=
  let ⟨_, h'⟩ := h.exists_isCompl_of_valuationRing
  finite_of_isCompl h'

theorem IsSaturatedSubmodule.free_of_valuationRing [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N :=
  haveI := h.finite_of_valuationRing
  free_of_finite_of_isTorsionFree_of_valuationRing R N

theorem IsSaturatedIn.finite_of_valuationRing {P N : Submodule R M} [Module.Finite R P]
    (h : IsSaturatedIn P N) : Module.Finite R N :=
  haveI := (isSaturatedIn_iff.1 h).2.finite_of_valuationRing
  Module.Finite.equiv (Submodule.submoduleOfEquivOfLe h.le)

end Valuation

universe u

example : ∃ N' : Submodule ℤ (ℤ × ℤ), IsCompl (Submodule.span ℤ {((1, 2) : ℤ × ℤ)}) N' :=
  isSaturatedSubmodule_span_one_two.exists_isCompl

end GlobalTheory
