import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfInjectiveModMaximalIdeal
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem mkQ_mem_smul_top_iff_mem_sup {A : Type} [CommRing A] (J I : Ideal A) (a : A) :
    Submodule.mkQ J a ∈ (I • ⊤ : Submodule A (A ⧸ J)) ↔ a ∈ J ⊔ I := by
  rw [← Submodule.range_mkQ J, LinearMap.range_eq_map, ← Submodule.map_smul'',
    ← Submodule.mem_comap, Submodule.comap_map_mkQ, smul_eq_mul, Ideal.mul_top]

theorem flat_quotient_sup_span_singleton (V A : Type) [CommRing V] [IsNoetherianRing V]
    [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A]
    [IsLocalHom (algebraMap V A)] (J : Ideal A) [Module.Flat V (A ⧸ J)] (r : A)
    (hr : ∀ a : A, r * a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A) →
      a ∈ J ⊔ (maximalIdeal V).map (algebraMap V A)) :
    Module.Flat V (A ⧸ (J ⊔ Ideal.span {r})) := by
  let u : (A ⧸ J) →ₗ[A] (A ⧸ J) := LinearMap.lsmul A (A ⧸ J) r
  have h := flat_coker_of_injective_mod_maximalIdeal V A (A ⧸ J) (A ⧸ J) u (by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J x
    rw [mkQ_mem_smul_top_iff_mem_sup]
    apply hr
    rw [← mkQ_mem_smul_top_iff_mem_sup]
    exact hx)
  have hu : LinearMap.range u = Submodule.map (Submodule.mkQ J) (Ideal.span {r}) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective J y
      exact ⟨r * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hb
      exact ⟨Submodule.mkQ J a, rfl⟩
  let e : ((A ⧸ J) ⧸ LinearMap.range u) ≃ₗ[A] (A ⧸ (J ⊔ Ideal.span {r})) :=
    (Submodule.quotEquivOfEq _ _ hu).trans
      (Submodule.quotientQuotientEquivQuotientSup J (Ideal.span {r}))
  exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm

theorem mem_sup_of_isSMulRegular_quotient_quotient {A : Type} [CommRing A] (I J : Ideal A) (r : A)
    (h : IsSMulRegular ((A ⧸ I) ⧸ (J • ⊤ : Submodule A (A ⧸ I))) r) (a : A)
    (ha : r * a ∈ J ⊔ I) : a ∈ J ⊔ I := by
  rw [sup_comm, ← mkQ_mem_smul_top_iff_mem_sup, ← Submodule.Quotient.mk_eq_zero] at ha ⊢
  apply h
  simp only [smul_zero]
  exact ha

theorem flat_quotient_ofList_of_isWeaklyRegular_closedFibre : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  intro V A _ _ _ _ _ _ _ _ _ rs _ hreg
  have key : ∀ i, i ≤ rs.length → Module.Flat V (A ⧸ Ideal.ofList (rs.take i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [List.take_zero, Ideal.ofList_nil]
      exact Module.Flat.of_linearEquiv
        ((Submodule.quotEquivOfEqBot (⊥ : Ideal A) rfl).restrictScalars V)
    | succ i ih =>
      intro hi
      have hi' : i < rs.length := hi
      haveI := ih hi'.le
      rw [List.take_succ_eq_append_getElem hi', Ideal.ofList_append, Ideal.ofList_singleton]
      exact flat_quotient_sup_span_singleton V A _ _
        (mem_sup_of_isSMulRegular_quotient_quotient _ _ _ (hreg.regular_mod_prev i hi'))
  have h := key rs.length le_rfl
  rwa [List.take_length] at h

end GlobalTheory
