import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Formalism.GaloisCohomology.Statement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

private lemma pairing_smul_left' {p : ℕ} [NeZero p] {M M' : Type} [AddCommGroup M] [AddCommGroup M']
    [Module (ZMod p) M] (β : M →+ M' →+ ZMod p) (a : ZMod p) (v : M) (m' : M') :
    β (a • v) m' = a * β v m' := by
  have h : a • v = a.val • v := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod p) a.val v
  rw [h, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem exists_sum_mul_of_finite_torsion (l : ℕ) [Fact l.Prime] (M M' : Type) [AddCommGroup M]
    [AddCommGroup M'] [Module (ZMod l) M] (β : M →+ M' →+ ZMod l) (S : Set M)
    (hS : S.Finite) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → M →+ ZMod l) (d : ι → M' →+ ZMod l),
      ∀ m ∈ S, ∀ m' : M', β m m' = ∑ k ∈ s, c k m * d k m' := by
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  refine ⟨_, hS.toFinset.biUnion (fun m => (b.repr m).support),
    fun i => (b.coord i).toAddMonoidHom, fun i => β (b i), ?_⟩
  intro m hm m'
  have hsub : (b.repr m).support ⊆ hS.toFinset.biUnion (fun m => (b.repr m).support) :=
    Finset.subset_biUnion_of_mem (fun m => (b.repr m).support) (hS.mem_toFinset.2 hm)
  have hm' : m = ∑ i ∈ (b.repr m).support, b.repr m i • b i := by
    conv_lhs => rw [← b.linearCombination_repr m]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  conv_lhs => rw [hm']
  rw [map_sum, AddMonoidHom.finset_sum_apply]
  simp only [pairing_smul_left', LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply]
  refine Finset.sum_subset hsub ?_
  intro k _ hk
  have hz : b.repr m k = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.2 h)
  rw [hz, zero_mul]

theorem inv_cup_pairing_of_inv_cup_characters : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (μ : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g m, μ g m = m) → ∀ (e : H2 μ →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) (I : Γ → Prop) (u : ZMod (l ^ 1)) (γ φ : Γ), (∀ z y : Γ → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = u * (z γ * y φ)) → ∀ (M M' : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M'], (∀ m : M, l • m = 0) → ∀ (β : M →+ M' →+ ZMod (l ^ 1)) (x : Γ → M) (y : Γ → M'), Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = β (x g) (y h)) → e (Submodule.Quotient.mk w) = u * β (x γ) (y φ) := by
  intro Γ _ _ _ _ l _ μ hμ e I u γ φ hchar M M' _ _ _ _ _ _ hl β x y hxc hyc hxa hya hyI w hw
  classical
  haveI hp : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : NeZero (l ^ 1) := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod (l ^ 1)) M :=
    AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
  have hfin : (Set.range x).Finite := (isCompact_range hxc).finite_of_discrete
  obtain ⟨ι, s, c, d, hdec⟩ :=
    exists_sum_mul_of_finite_torsion (l ^ 1) M M' β (Set.range x) hfin
  have hmem : ∀ k, (fun q : Γ × Γ => c k (x q.1) * d k (y q.2)) ∈ Z2 μ := by
    intro k
    rw [mem_cocycles2]
    refine ⟨?_, ?_⟩
    · exact ((continuous_of_discreteTopology.comp hxc).comp continuous_fst).mul
        ((continuous_of_discreteTopology.comp hyc).comp continuous_snd)
    · intro g h k'
      simp only [hμ, hxa, hya, map_add]
      ring
  let W : ι → Z2 μ := fun k => ⟨_, hmem k⟩
  have hWsum : w = ∑ k ∈ s, W k := by
    apply Subtype.ext
    funext q
    rcases q with ⟨g, h⟩
    rw [Submodule.coe_sum, Finset.sum_apply, hw g h]
    exact hdec (x g) ⟨g, rfl⟩ (y h)
  have hW : ∀ k, e (Submodule.Quotient.mk (W k)) = u * (c k (x γ) * d k (y φ)) := fun k =>
    hchar (fun g => c k (x g)) (fun g => d k (y g))
      (continuous_of_discreteTopology.comp hxc) (continuous_of_discreteTopology.comp hyc)
      (fun g h => by simp only [hxa, map_add]) (fun g h => by simp only [hya, map_add])
      (fun g hg => by simp only [hyI g hg, map_zero]) (W k) (fun g h => rfl)
  have hq : (Submodule.Quotient.mk (∑ k ∈ s, W k) : H2 μ) =
      ∑ k ∈ s, (Submodule.Quotient.mk (W k) : H2 μ) :=
    map_sum (Submodule.mkQ _) W s
  rw [hWsum, hq, map_sum]
  simp only [hW]
  rw [← Finset.mul_sum, ← hdec (x γ) ⟨γ, rfl⟩ (y φ)]

end GlobalTheory
