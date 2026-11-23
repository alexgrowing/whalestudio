import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

section Idx

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

noncomputable def idx (N F : Submodule R M) : ℕ := N.toAddSubgroup.relIndex F.toAddSubgroup

theorem idx_eq_card (N F : Submodule R M) : idx N F = Nat.card (F ⧸ N.comap F.subtype) := rfl

theorem idx_mul {N F G : Submodule R M} (h1 : N ≤ F) (h2 : F ≤ G) : idx N F * idx F G = idx N G :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2

theorem idx_sup {N F G : Submodule R M} (h : N ≤ F) (hd : Disjoint F G) :
    idx (N ⊔ G) (F ⊔ G) = idx N F := by
  rw [idx_eq_card, idx_eq_card]
  let φ : F →ₗ[R] (↥(F ⊔ G) ⧸ (N ⊔ G).comap (F ⊔ G).subtype) :=
    ((N ⊔ G).comap (F ⊔ G).subtype).mkQ ∘ₗ Submodule.inclusion le_sup_left
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub,
      Submodule.coe_inclusion]
    have : f - (f + g) = -g := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.mem_sup_right hg)
  have hker : LinearMap.ker φ = N.comap F.subtype := by
    ext ⟨x, hx⟩
    simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]
    constructor
    · intro hxs
      obtain ⟨n, hn, g, hg, hng⟩ := Submodule.mem_sup.mp hxs
      have hgF : g ∈ F := by
        have : g = x - n := by rw [← hng]; abel
        rw [this]
        exact F.sub_mem hx (h hn)
      have hg0 : g = 0 := by
        have := hd.le_bot ⟨hgF, hg⟩
        simpa using this
      rw [← hng, hg0, add_zero]
      exact hn
    · intro hn
      exact Submodule.mem_sup_left hn
  rw [← hker]
  exact (Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv).symm

end Idx

theorem deg_eq (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier) {ι : Type} [Fintype ι]
    [DecidableEq ι] {s : ι → E.carrier} (hs : LinearIndependent (𝓞 K) s) (hm : ∀ i, s i ∈ F)
    (hc : Fintype.card ι = E.rank F) :
    idx (Submodule.span (𝓞 K) (Set.range s)) F ≠ 0 ∧
      E.degree F = Real.log (idx (Submodule.span (𝓞 K) (Set.range s)) F) -
        (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet E.metric σ s) := by
  let s' : ι → F := fun i => ⟨s i, hm i⟩
  have hs' : LinearIndependent (𝓞 K) s' := LinearIndependent.of_comp F.subtype hs
  have hspan : Submodule.span (𝓞 K) (Set.range s') =
      (Submodule.span (𝓞 K) (Set.range s)).comap F.subtype := by
    have e : (Submodule.span (𝓞 K) (Set.range s')).map F.subtype = Submodule.span (𝓞 K) (Set.range s) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← e, Submodule.comap_map_eq_of_injective F.injective_subtype]
  have hfin : Finite (F ⧸ Submodule.span (𝓞 K) (Set.range s')) := finite_quotient_span hs' hc
  have hdeg := E.degree_eq_of_linearIndependent F hs' hc
  rw [hspan] at hfin hdeg
  refine ⟨?_, ?_⟩
  · rw [idx_eq_card]
    exact Nat.card_pos.ne'
  · rw [hdeg, idx_eq_card]

theorem exists_fam (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier) :
    ∃ s : Fin (E.rank F) → E.carrier, LinearIndependent (𝓞 K) s ∧ ∀ i, s i ∈ F := by
  obtain ⟨f, hf⟩ := E.exists_linearIndependent_rank F
  exact ⟨fun i => (f i : E.carrier), hf.map' F.subtype F.ker_subtype, fun i => (f i).2⟩

theorem span_le_of_mem {R M ι : Type} [Ring R] [AddCommGroup M] [Module R M] {s : ι → M}
    {F : Submodule R M} (h : ∀ i, s i ∈ F) : Submodule.span R (Set.range s) ≤ F :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr h)

theorem rank_sup (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier} (hd : Disjoint F G) :
    E.rank (F ⊔ G) = E.rank F + E.rank G := by
  have h := Submodule.rank_sup_add_rank_inf_eq F G
  rw [disjoint_iff.mp hd, rank_bot, add_zero] at h
  unfold HermitianBundle.rank Module.finrank
  rw [h, Cardinal.toNat_add (Module.rank_lt_aleph0 (𝓞 K) F) (Module.rank_lt_aleph0 (𝓞 K) G)]

theorem rank_map (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier)
    (hφ : Function.Injective φ) (F : Submodule (𝓞 K) E.carrier) : E'.rank (F.map φ) = E.rank F :=
  (Submodule.equivMapOfInjective φ hφ F).finrank_eq.symm

theorem rank_pos (E : HermitianBundle.{0} K) {F : Submodule (𝓞 K) E.carrier} (hF : F ≠ ⊥) :
    0 < E.rank F := by
  unfold HermitianBundle.rank
  haveI : Nontrivial F := Submodule.nontrivial_iff_ne_bot.mpr hF
  exact Module.finrank_pos

end CoverDenseAlt
