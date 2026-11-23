import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts

open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open scoped ContDiff

private def UpperTheory.V.Cj.A.idxEquiv (Γ J : Type) : Γ × J ≃ Idx Γ J where
  toFun x := ⟨x.1, x.2⟩
  invFun i := (i.g, i.j)
  left_inv _ := rfl
  right_inv _ := rfl

theorem UpperTheory.V.Cj.A.partProd :
    PartProd := by
  intro Γ V S J _ _ _ d G u hu ψ hψs hψf hψ1
  obtain ⟨hus, huf, hu1⟩ := hu
  have hlf : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, {i : Idx Γ J | ∃ x ∈ N,
      u ((G.σ i.g⁻¹) s) ((G.ρ i.g⁻¹) x) * ψ ((G.σ i.g⁻¹) s) i.j ((G.ρ i.g⁻¹) x) ≠ 0}.Finite := by
    intro s p hp
    obtain ⟨N₁, hN₁, hF⟩ := huf s p hp
    have key : ∀ γ : Γ, ∃ M ∈ nhds p,
        {j | ∃ x ∈ M, ψ ((G.σ γ⁻¹) s) j ((G.ρ γ⁻¹) x) ≠ 0}.Finite := by
      intro γ
      obtain ⟨M, hM, hMf⟩ := hψf ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) p) (G.maps _ p hp)
      refine ⟨(G.ρ γ⁻¹) ⁻¹' M, (G.ρ γ⁻¹).continuous.continuousAt.preimage_mem_nhds hM, ?_⟩
      refine hMf.subset ?_
      rintro j ⟨x, hx, hne⟩
      exact ⟨_, hx, hne⟩
    choose M hM hMf using key
    refine ⟨N₁ ∩ ⋂ γ ∈ hF.toFinset, M γ, ?_, ?_⟩
    · exact Filter.inter_mem hN₁ ((Filter.biInter_finset_mem _).2 fun γ _ => hM γ)
    · refine ((hF.toFinset.finite_toSet.biUnion fun γ _ =>
        (Set.finite_singleton γ).prod (hMf γ)).image (idxEquiv Γ J)).subset ?_
      rintro ⟨g, j⟩ ⟨x, ⟨hx1, hx2⟩, hne⟩
      have hu0 : u ((G.σ g⁻¹) s) ((G.ρ g⁻¹) x) ≠ 0 := left_ne_zero_of_mul hne
      have hψ0 : ψ ((G.σ g⁻¹) s) j ((G.ρ g⁻¹) x) ≠ 0 := right_ne_zero_of_mul hne
      have hgF : g ∈ hF.toFinset := hF.mem_toFinset.2 ⟨x, hx1, hu0⟩
      refine ⟨(g, j), Set.mem_biUnion (x := g) hgF ⟨Set.mem_singleton _, x, ?_, hψ0⟩, rfl⟩
      exact Set.mem_iInter₂.1 hx2 g hgF
  refine ⟨?_, hlf, ?_, ?_⟩
  · intro i s
    have hmap : Set.MapsTo (G.ρ i.g⁻¹) G.Y G.Y := fun p hp => G.maps _ p hp
    exact ((hus _).comp (G.ρ i.g⁻¹).contDiff.contDiffOn hmap).mul
      ((hψs _ _).comp (G.ρ i.g⁻¹).contDiff.contDiffOn hmap)
  · intro s p hp
    have hfin : (Function.support fun x : Γ × J =>
        u ((G.σ x.1⁻¹) s) ((G.ρ x.1⁻¹) p) * ψ ((G.σ x.1⁻¹) s) x.2 ((G.ρ x.1⁻¹) p)).Finite := by
      obtain ⟨N, hN, hNf⟩ := hlf s p hp
      refine (hNf.preimage (idxEquiv Γ J).injective.injOn).subset ?_
      intro x hx
      exact ⟨p, mem_of_mem_nhds hN, hx⟩
    rw [← finsum_comp_equiv (idxEquiv Γ J)]
    show ∑ᶠ x : Γ × J, u ((G.σ x.1⁻¹) s) ((G.ρ x.1⁻¹) p) *
      ψ ((G.σ x.1⁻¹) s) x.2 ((G.ρ x.1⁻¹) p) = 1
    rw [finsum_curry _ (by exact hfin)]
    have hin : ∀ a : Γ, ∑ᶠ b : J, u ((G.σ a⁻¹) s) ((G.ρ a⁻¹) p) * ψ ((G.σ a⁻¹) s) b ((G.ρ a⁻¹) p) =
        u ((G.σ a⁻¹) s) ((G.ρ a⁻¹) p) := by
      intro a
      rw [← mul_finsum, hψ1 _ _ (G.maps _ _ hp), mul_one]
    rw [finsum_congr hin]
    exact hu1 s p hp
  · intro γ i s p
    have h1 : (G.σ γ⁻¹) ((G.σ γ) s) = s := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
    have h2 : (G.ρ γ⁻¹) ((G.ρ γ) p) = p := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
    show u ((G.σ (γ * i.g)⁻¹) ((G.σ γ) s)) ((G.ρ (γ * i.g)⁻¹) ((G.ρ γ) p)) *
      ψ ((G.σ (γ * i.g)⁻¹) ((G.σ γ) s)) i.j ((G.ρ (γ * i.g)⁻¹) ((G.ρ γ) p)) = _
    rw [mul_inv_rev, map_mul, map_mul, Equiv.Perm.mul_apply, ContinuousLinearMap.mul_apply, h1, h2]
