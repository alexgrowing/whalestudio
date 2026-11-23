import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

namespace GlobalTheory.FinTrace

theorem stabilizer_equiv_locPart : ∀ (G : Type) [Group G] (H K : Subgroup G) (x : G),
    Nonempty (MulAction.stabilizer H (QuotientGroup.mk x : G ⧸ K) ≃ GlobalTheory.LKLoc.locPart H K x) := by
  intro G _ H K x
  have hmem : ∀ h : H, h ∈ MulAction.stabilizer H (QuotientGroup.mk x : G ⧸ K) ↔
      (h : G) ∈ GlobalTheory.LKLoc.locPart H K x := by
    intro h
    rw [MulAction.mem_stabilizer_iff]
    show ((h : G) • (QuotientGroup.mk x : G ⧸ K)) = _ ↔ _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    simp only [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      SetLike.coe_mem, true_and]
    constructor
    · intro hk
      refine ⟨_, K.inv_mem hk, ?_⟩
      group
    · rintro ⟨k, hk, e⟩
      rw [← e]
      convert K.inv_mem hk using 1
      group
  exact ⟨{ toFun := fun h => ⟨h.1, (hmem h.1).1 h.2⟩
           invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hmem _).2 g.2⟩
           left_inv := fun h => rfl
           right_inv := fun g => rfl }⟩

theorem finite_support_conj : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (f : G → ℂ), (∀ k ∈ K, ∀ g, f (g * k) = f g) →
    (Function.support fun q : G ⧸ K => f (Quotient.out q)).Finite → ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x) →
    (Function.support fun γ : Γ => f (x⁻¹ * γ * x)).Finite := by
  intro G _ Γ K f hR hs x hx
  let π : Γ → G ⧸ K := fun γ => QuotientGroup.mk (x⁻¹ * γ * x)
  have hmaps : Set.MapsTo π (Function.support fun γ : Γ => f (x⁻¹ * γ * x)) (Function.support fun q : G ⧸ K => f q.out) := by
    intro γ hγ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (x⁻¹ * γ * x)
    simp only [Function.mem_support, π, hk, hR _ k.2] at hγ ⊢
    exact hγ
  refine Set.Finite.of_finite_fibers π (hs.subset (Set.image_subset_iff.2 hmaps)) ?_
  haveI := hx
  intro q _
  by_cases hne : (π ⁻¹' {q}).Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hne
    have hsub : π ⁻¹' {q} ⊆ (fun l : GlobalTheory.LKLoc.locPart Γ K x => γ₀ * ⟨l.1, l.2.1⟩) '' Set.univ := by
      intro γ hγ
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hγ hγ₀
      have h := hγ₀.trans hγ.symm
      rw [QuotientGroup.eq] at h
      refine ⟨⟨(γ₀⁻¹ * γ : Γ), (γ₀⁻¹ * γ : Γ).2, ?_⟩, trivial, Subtype.ext (by simp)⟩
      refine ⟨_, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact ((Set.finite_univ.image _).subset hsub).subset Set.inter_subset_right
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.inter_empty]
    exact Set.finite_empty

end GlobalTheory.FinTrace
