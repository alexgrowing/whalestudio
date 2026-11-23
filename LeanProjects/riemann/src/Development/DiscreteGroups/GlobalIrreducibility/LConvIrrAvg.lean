import Development.DiscreteGroups.GlobalIrreducibility.LConvIrrComm

noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

def fixSub (K : Subgroup G) : Submodule ℂ M where
  carrier := {a | ∀ κ ∈ K, ρ κ a = a}
  add_mem' {a b} ha hb κ hκ := by rw [map_add, ha κ hκ, hb κ hκ]
  zero_mem' κ _ := map_zero _
  smul_mem' c a ha κ hκ := by rw [map_smul, ha κ hκ]

include hinv in
theorem avg_exists [TopologicalSpace G] [IsTopologicalGroup G] (hsm : IsSmooth ρ) (Z : Submodule ℂ M)
    (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z) (K : Subgroup G) (hKc : IsCompact (K : Set G)) (x : M)
    (hx : ∀ κ ∈ K, ρ κ x = x) (z : M) (hz : z ∈ Z) :
    ∃ a ∈ Z, (∀ κ ∈ K, ρ κ a = a) ∧
      dist (iota B hB x) (iota B hB a) ≤ dist (iota B hB x) (iota B hB z) := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hf : Continuous fun g : G => ρ g z := by
    refine continuous_discrete_rng.2 fun b => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨(fun h => g⁻¹ * h) ⁻¹' {h | ρ h z = z}, fun h hh => ?_,
      (continuous_mul_left g⁻¹).isOpen_preimage _ (hsm z), ?_⟩
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] at hh hg ⊢
      rw [← hg, show h = g * (g⁻¹ * h) by group, rho_mul, hh]
    · simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, rho_one]
  have hfin : ((fun g : G => ρ g z) '' (K : Set G)).Finite := (hKc.image hf).finite_of_discrete
  set O := hfin.toFinset with hO
  have hmem : ∀ m, m ∈ O ↔ ∃ k ∈ K, ρ k z = m := fun m => by
    rw [hO, Set.Finite.mem_toFinset]; rfl
  have hzO : z ∈ O := (hmem z).2 ⟨1, K.one_mem, rho_one ρ z⟩
  have hcard : (O.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  have hcardC : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨z, hzO⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ m ∈ O, m, Z.smul_mem _ (Z.sum_mem fun m hm => ?_), fun κ hκ => ?_, ?_⟩
  · obtain ⟨k, _, rfl⟩ := (hmem m).1 hm
    exact hZ k z hz
  · rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (fun m => ρ κ m) (fun m => ρ κ⁻¹ m) (fun m hm => ?_) (fun m hm => ?_)
      (fun m _ => rho_inv ρ κ m) (fun m _ => ?_) (fun _ _ => rfl)
    · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      exact (hmem _).2 ⟨κ * k, K.mul_mem hκ hk, rho_mul ρ κ k z⟩
    · obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      exact (hmem _).2 ⟨κ⁻¹ * k, K.mul_mem (K.inv_mem hκ) hk, rho_mul ρ κ⁻¹ k z⟩
    · simp
  · have hdist : ∀ m ∈ O, ‖iota B hB x - iota B hB m‖ = ‖iota B hB x - iota B hB z‖ := by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := (hmem m).1 hm
      have e : iota B hB x - iota B hB (ρ k z) = pi B hB ρ hinv k (iota B hB x - iota B hB z) := by
        rw [map_sub, pi_iota, pi_iota, hx k hk]
      rw [e, norm_pi]
    have hsum : iota B hB x - iota B hB ((O.card : ℂ)⁻¹ • ∑ m ∈ O, m) =
        (O.card : ℂ)⁻¹ • ∑ m ∈ O, (iota B hB x - iota B hB m) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, map_smul, map_sum,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcardC, one_smul]
    rw [dist_eq_norm, dist_eq_norm, hsum, norm_smul]
    calc ‖((O.card : ℂ))⁻¹‖ * ‖∑ m ∈ O, (iota B hB x - iota B hB m)‖
        ≤ ‖((O.card : ℂ))⁻¹‖ * ∑ m ∈ O, ‖iota B hB x - iota B hB m‖ := by gcongr; exact norm_sum_le _ _
      _ = ‖((O.card : ℂ))⁻¹‖ * (O.card * ‖iota B hB x - iota B hB z‖) := by
          rw [Finset.sum_congr rfl hdist, Finset.sum_const, nsmul_eq_mul]
      _ = ‖iota B hB x - iota B hB z‖ := by
          rw [norm_inv, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
