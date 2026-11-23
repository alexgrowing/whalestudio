import Mathlib
import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataAmbForm
open Formalism.BasicNotions Classical

namespace GlobalTheory.KFiMu0

theorem fi_eq_range' {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) (j : ℕ) : M.Fi j = Submodule.span ℂ (Set.range (M.emb j)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [← (M.emb_basis j).2]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    rw [← (M.emb_basis j).2, ← (M.lat j).b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem carries_one {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc} (h : C' = C)
    {A : ColumnsAtT R C} {P : PeriodMap R C} {A' : ColumnsAtT R C'} {P' : PeriodMap R C'}
    (M : MemberForms LL embLL Pl Tau hc C A P) (M' : MemberForms LL embLL Pl Tau hc C' A' P')
    (e : ∀ j, j ≤ R.m → ((M.lat j).V ≃ₗ[LL] (M'.lat j).V)) (he : ∀ j hj x, HEq (M'.emb j (e j hj x)) (M.emb j x))
    (i : ℕ) (hi : i < R.m) (H : ∀ φ ∈ M'.Fi i, C'.K i φ ∈ M'.Fi (i + 1)) :
    ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  subst h
  have k : ∀ j, j ≤ R.m → M.Fi j = M'.Fi j := fun j hj => by
    rw [fi_eq_range', fi_eq_range']
    congr 1
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e j hj x, eq_of_heq (he j hj x)⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e j hj).surjective y
      exact ⟨x, (eq_of_heq (he j hj x)).symm⟩
  intro φ hφ
  rw [k _ hi.le] at hφ
  rw [k _ hi]
  exact H φ hφ

theorem memberForms_stable_of_reference_tuple : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word), ∀ i < D.R.m,
    (∀ φ ∈ (T.fm u D.what₂.mu0).Fi i, (D.chTw u D.what₂.mu0).K i φ ∈ (T.fm u D.what₂.mu0).Fi (i + 1)) →
    ∀ φ ∈ (D.fm u).Fi i, (D.mem u).C.K i φ ∈ (D.fm u).Fi (i + 1) :=
  fun D T u i hi H => carries_one (D.memberColumns_twistedChain_base u) (D.fm u) (T.fm u D.what₂.mu0) (T.eMu0 u) (T.eMu0_emb u) i hi H

end GlobalTheory.KFiMu0
