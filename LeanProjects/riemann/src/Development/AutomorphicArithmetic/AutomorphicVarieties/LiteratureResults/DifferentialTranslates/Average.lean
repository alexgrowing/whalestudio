import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AvgMem

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} {G : Geo Γ V S d} {u : S → V → ℝ}

end

theorem average : Average := by
  intro Γ V S _ _ _ d G u hu q
  have hu' := hu
  obtain ⟨hsm, hfin, hone⟩ := hu
  have hfs : ∀ (c : Γ → G.Om q) s p, Function.HasFiniteSupport
      (fun g => u (G.σ g⁻¹ s) (G.ρ g⁻¹ p) • (c g).1 s p) := by
    intro c s p
    by_cases hp : p ∈ G.Y
    · obtain ⟨N, hN, hNfin⟩ := hfin s p hp
      refine hNfin.subset ?_
      intro g hg
      refine ⟨p, mem_of_mem_nhds hN, ?_⟩
      intro h0
      apply hg
      simp only [h0, zero_smul]
    · refine Set.finite_empty.subset ?_
      intro g hg
      apply hg
      simp only [((c g).2 _).2 _ hp, smul_zero]
  let A : (Γ → G.Om q) →ₗ[ℂ] G.Om q :=
    { toFun := fun c => ⟨fun s p => ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (c γ).1 s p,
        avgMem Γ V S d G u hu' q c⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ + b γ).1 s p =
          ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ).1 s p + ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (b γ).1 s p
        simp only [Submodule.coe_add, Pi.add_apply, smul_add]
        exact finsum_add_distrib (hfs a s p) (hfs b s p)
      map_smul' := by
        intro z a
        apply Subtype.ext
        funext s p
        show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (z • a γ).1 s p =
          z • ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ).1 s p
        have hm := map_finsum (DistribMulAction.toAddMonoidHom (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) z)
          (hfs a s p)
        simp only [DistribMulAction.toAddMonoidHom_apply] at hm
        rw [hm]
        congr 1
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply]
        rw [smul_comm] }
  refine ⟨A, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext s p
    show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • x.1 s p = x.1 s p
    by_cases hp : p ∈ G.Y
    · rw [← finsum_smul, hone s p hp, one_smul]
    · have hx0 : x.1 s p = 0 := (x.2 s).2 p hp
      simp [hx0]
  · intro γ c
    apply Subtype.ext
    funext s p
    show G.tr q γ (∑ᶠ g, u (G.σ g⁻¹ (G.σ γ⁻¹ s)) (G.ρ g⁻¹ (G.ρ γ⁻¹ p)) • (c g).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
      = ∑ᶠ g, u (G.σ g⁻¹ s) (G.ρ g⁻¹ p) • G.tr q γ ((c (γ⁻¹ * g)).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [map_finsum (G.tr q γ) (hfs c _ _)]
    conv_rhs => rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
    congr 1
    funext h
    simp [_root_.mul_inv_rev, map_mul, Equiv.Perm.mul_apply]

end UpperTheory.V.Lit.Dr
