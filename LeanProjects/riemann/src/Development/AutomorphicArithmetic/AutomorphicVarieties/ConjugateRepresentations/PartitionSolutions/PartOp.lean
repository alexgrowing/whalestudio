import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartMem

noncomputable section

open UpperTheory.V.Lit UpperTheory.V.Lit.Dr

namespace UpperTheory.V.Cj.A

section

variable {Γ V S I : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] {d : ℕ}
  {G : Dr.Geo Γ V S d} {φ : I → S → V → ℝ}

private theorem part_fin_φ (hφ : IsPart G φ) (s : S) {p : V} (hp : p ∈ G.Y) :
    (Function.support fun i : I => φ i s p).Finite := by
  obtain ⟨N, hN, hf⟩ := hφ.locFin s p hp
  exact hf.subset fun i hi => ⟨p, mem_of_mem_nhds hN, hi⟩

private theorem part_fin (hφ : IsPart G φ) {q : ℕ} (c : I → G.Om q) (s : S) (p : V) :
    (Function.support fun i : I => φ i s p • (c i).1 s p).Finite := by
  by_cases hp : p ∈ G.Y
  · refine (part_fin_φ hφ s hp).subset fun i hi h0 => hi ?_
    beta_reduce at h0 ⊢
    rw [h0, zero_smul]
  · refine Set.finite_empty.subset fun i hi => hi ?_
    beta_reduce
    rw [((c i).2 s).2 p hp, smul_zero]

private theorem part_shift (hφ : IsPart G φ) (γ : Γ) (i : I) (s : S) (p : V) :
    φ (γ • i) s p = φ i (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by
  have h := hφ.equiv γ⁻¹ (γ • i) s p
  rw [inv_smul_smul] at h
  exact h.symm

end

theorem partOp : PartOp := by
  intro Γ V S I _ _ _ _ d G φ hφ q
  refine ⟨{ toFun := fun c => ⟨_, partMem Γ V S I d G φ hφ q c⟩, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro c c'
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    simp only [Pi.add_apply, Submodule.coe_add, smul_add]
    exact finsum_add_distrib (part_fin hφ c s p) (part_fin hφ c' s p)
  · intro a c
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    rw [smul_finsum' a (part_fin hφ c s p)]
    exact finsum_congr fun i => smul_comm _ _ _
  · intro x
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    change ∑ᶠ i : I, φ i s p • x.1 s p = x.1 s p
    by_cases hp : p ∈ G.Y
    · rw [← finsum_smul' (part_fin_φ hφ s hp), hφ.sum_one s p hp, one_smul]
    · simp [(x.2 s).2 p hp]
  · intro γ c
    refine Subtype.ext (funext fun s => funext fun p => Eq.symm ?_)
    change G.tr q γ (∑ᶠ i : I, φ i (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (c i).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) =
      ∑ᶠ i : I, φ i s p • G.tr q γ ((c (γ⁻¹ • i)).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [map_finsum (G.tr q γ) (part_fin hφ c _ _)]
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm γ))
    refine finsum_congr fun i => ?_
    rw [MulAction.toPerm_apply, inv_smul_smul, part_shift hφ, map_smul]
  · intro c s p h
    change ∑ᶠ i : I, φ i s p • (c i).1 s p = 0
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    by_cases h0 : φ i s p = 0
    · rw [h0, zero_smul]
    · rw [h i h0, smul_zero]

end UpperTheory.V.Cj.A
