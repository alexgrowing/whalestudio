import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowG

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem unipotentSpace_le_baseSubspace (μ) : S.Usp μ ≤ S.V0 μ := inf_le_left

theorem sub_projQ_mem (μ) {x : S.Amb μ} (hx : x ∈ S.V0 μ) : x - (S.Qsp μ).starProjection x ∈ S.Usp μ := by
  set u := (S.Usp μ).starProjection x with hu
  have huU : u ∈ S.Usp μ := Submodule.starProjection_apply_mem _ _
  have hq : x - u ∈ S.Qsp μ :=
    ⟨Submodule.sub_mem _ hx (unipotentSpace_le_baseSubspace S μ huU), Submodule.sub_starProjection_mem_orthogonal x⟩
  have hp : (S.Qsp μ).starProjection x = x - u := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hq fun w hw => ?_
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal huU hw.2
  rw [hp, sub_sub_cancel]
  exact huU

theorem RRset_gen (μ) : S.RRset μ = S.iota μ '' ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ))) := by
  unfold RowSide.RRset RowSide.LamSet
  rw [Set.image_image]
  refine Set.image_congr fun x hx => ?_
  have h : S.iota μ (x - (S.Qsp μ).starProjection x) = 0 := (sub_projQ_mem S μ hx.2).2
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

variable {μ : D.what₂.Tup} (s : EE →ₗ[ℂ] S.Amb μ) (hs : ∀ y, S.iota μ (s y) = y)
  (hV : ∀ y, s y ∈ S.V0 μ) (hU : ∀ y, ∀ u ∈ S.Usp μ, inner ℂ u (s y) = 0)
  (hiso : ∀ y z, inner ℂ (s y) (s z) = inner ℂ y z)

include hs hV hU in

theorem mem_Qsp_iff (x : S.Amb μ) : x ∈ S.Qsp μ ↔ x = s (S.iota μ x) := by
  have hsQ : ∀ y, s y ∈ S.Qsp μ := fun y => ⟨hV y, (Submodule.mem_orthogonal _ _).mpr (hU y)⟩
  constructor
  · intro hx
    have h1 : x - s (S.iota μ x) ∈ S.Usp μ :=
      ⟨Submodule.sub_mem _ hx.1 (hV _),
        (show S.iota μ (x - s (S.iota μ x)) = 0 by rw [map_sub, hs, sub_self])⟩
    have h2 : x - s (S.iota μ x) ∈ (S.Usp μ)ᗮ := Submodule.sub_mem _ hx.2 (hsQ _).2
    have h3 := Submodule.inner_right_of_mem_orthogonal h1 h2
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)
  · intro hx
    rw [hx]; exact hsQ _

include hs hV hU in
theorem iotaQ_bij' : Function.Bijective (S.iotaQ μ) := by
  refine ⟨fun a b h => Subtype.ext ?_, fun y => ⟨⟨s y, (mem_Qsp_iff S s hs hV hU _).mpr (by rw [hs])⟩, hs y⟩⟩
  rw [(mem_Qsp_iff S s hs hV hU _).mp a.2, (mem_Qsp_iff S s hs hV hU _).mp b.2]
  exact congrArg s h

include hs hV hU hiso in
theorem iotaQ_adj' : S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ) = LinearMap.id := by
  ext x
  refine ext_inner_right ℂ fun y => ?_
  have hz : s y ∈ S.Qsp μ := (mem_Qsp_iff S s hs hV hU _).mpr (by rw [hs])
  set q := LinearMap.adjoint (S.iotaQ μ) x with hq
  have h1 : inner ℂ q (⟨s y, hz⟩ : S.Qsp μ) = inner ℂ x (S.iotaQ μ ⟨s y, hz⟩) :=
    LinearMap.adjoint_inner_left _ _ _
  have h2 : S.iotaQ μ ⟨s y, hz⟩ = y := hs y
  rw [h2] at h1
  show inner ℂ (S.iota μ (q : S.Amb μ)) y = inner ℂ x y
  rw [← h1, ← hiso, ← (mem_Qsp_iff S s hs hV hU _).mp q.2]
  rfl

end Gen

end Formalism.BasicNotions.Examples₂.NZ
