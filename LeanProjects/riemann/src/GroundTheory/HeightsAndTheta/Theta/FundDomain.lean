import Mathlib

open MeasureTheory Set Topology

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_isOpen_inter_subgroup_eq_one (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ γ ∈ Γ, γ ∈ W → γ = 1 := by
  have h1 : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp h1
  refine ⟨W, hW, ?_, ?_⟩
  · have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := by rw [hWeq]; rfl
    simpa using this
  · intro γ hγ hγW
    have : (⟨γ, hγ⟩ : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := hγW
    rw [hWeq] at this
    simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp this)

variable [LocallyCompactSpace G]

theorem exists_isOpen_small (Γ : Subgroup G) [DiscreteTopology Γ] (c : G) :
    ∃ V : Set G, IsOpen V ∧ c ∈ V ∧ (∃ L, IsCompact L ∧ V ⊆ L) ∧
      ∀ γ ∈ Γ, ∀ x ∈ V, γ * x ∈ V → γ = 1 := by
  obtain ⟨W, hWo, hW1, hWΓ⟩ := exists_isOpen_inter_subgroup_eq_one Γ
  have hcont : Continuous fun p : G × G => p.1 * p.2⁻¹ := by fun_prop
  have hmem : (c, c) ∈ (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' W := by simpa using hW1
  obtain ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hsub⟩ :=
    isOpen_prod_iff.mp (hWo.preimage hcont) c c hmem
  obtain ⟨L, hL, hLn⟩ := exists_compact_mem_nhds c
  refine ⟨U₁ ∩ U₂ ∩ interior L, (hU₁.inter hU₂).inter isOpen_interior,
    ⟨⟨hc₁, hc₂⟩, mem_interior_iff_mem_nhds.mpr hLn⟩, ⟨L, hL, fun x hx => interior_subset hx.2⟩, ?_⟩
  intro γ hγ x hx hγx
  apply hWΓ γ hγ
  have : (γ * x, x) ∈ U₁ ×ˢ U₂ := ⟨hγx.1.1, hx.1.2⟩
  simpa using hsub this

def saturate (Γ : Subgroup G) (A : Set G) : Set G := {y | ∃ γ ∈ Γ, γ⁻¹ * y ∈ A}

theorem isOpen_saturate (Γ : Subgroup G) {A : Set G} (hA : IsOpen A) : IsOpen (saturate Γ A) := by
  have : saturate Γ A = ⋃ γ : Γ, (fun y => (γ : G)⁻¹ * y) ⁻¹' A := by
    ext y; simp [saturate]
  rw [this]
  exact isOpen_iUnion fun γ => hA.preimage (by fun_prop)

def firstHit (Γ : Subgroup G) (A : ℕ → Set G) : Set G :=
  ⋃ i, (A i \ saturate Γ (⋃ j < i, A j))

theorem measurableSet_firstHit [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    {A : ℕ → Set G} (hA : ∀ i, IsOpen (A i)) : MeasurableSet (firstHit Γ A) := by
  refine MeasurableSet.iUnion fun i => (hA i).measurableSet.diff ?_
  exact (isOpen_saturate Γ (isOpen_biUnion fun j _ => hA j)).measurableSet

theorem existsUnique_mem_firstHit (Γ : Subgroup G) (A : ℕ → Set G)
    (hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1)
    (hcov : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i) (x : G) :
    ∃! γ : Γ, γ • x ∈ firstHit Γ A := by
  classical
  have hex : ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i := hcov x
  let i₀ := Nat.find hex
  obtain ⟨γ, hγ, hγx⟩ := Nat.find_spec hex
  have hmin : ∀ j < i₀, ∀ δ ∈ Γ, δ * x ∉ A j := fun j hj δ hδ hδx =>
    Nat.find_min hex hj ⟨δ, hδ, hδx⟩
  have hγF : (γ : G) * x ∈ firstHit Γ A := by
    refine mem_iUnion.mpr ⟨i₀, hγx, ?_⟩
    rintro ⟨δ, hδ, hδy⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hδy
    obtain ⟨hj, hjA⟩ := mem_iUnion.mp hj
    refine hmin j hj (δ⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem hδ) hγ) ?_
    simpa [mul_assoc] using hjA
  refine ⟨⟨γ, hγ⟩, ?_, ?_⟩
  · show ((⟨γ, hγ⟩ : Γ) • x ∈ firstHit Γ A)
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hγF
  ·
    have key : ∀ (α β : Γ), (α : G) * x ∈ firstHit Γ A → (β : G) * x ∈ firstHit Γ A →
        ∀ i i', (α : G) * x ∈ A i \ saturate Γ (⋃ j < i, A j) →
          (β : G) * x ∈ A i' \ saturate Γ (⋃ j < i', A j) → i ≤ i' := by
      intro α β _ _ i i' hα hβ
      by_contra hlt'
      have hlt := not_le.mp hlt'
      apply hα.2
      refine ⟨(α : G) * (β : G)⁻¹, Γ.mul_mem α.2 (Γ.inv_mem β.2), ?_⟩
      refine mem_iUnion₂.mpr ⟨i', hlt, ?_⟩
      simpa [mul_assoc] using hβ.1
    intro β hβ
    rw [Subgroup.smul_def, smul_eq_mul] at hβ
    obtain ⟨i, hi⟩ := mem_iUnion.mp hβ
    obtain ⟨i', hi'⟩ := mem_iUnion.mp hγF
    have h1 := key β ⟨γ, hγ⟩ hβ hγF i i' hi hi'
    have h2 := key ⟨γ, hγ⟩ β hγF hβ i' i hi' hi
    have hii : i = i' := le_antisymm h1 h2
    subst hii
    have hmul := hinj i ((γ : G) * (β : G)⁻¹) (Γ.mul_mem hγ (Γ.inv_mem β.2)) _ hi.1
      (by simpa [mul_assoc] using hi'.1)
    apply Subtype.ext
    have : (γ : G) = β := by
      have := congrArg (· * (β : G)) hmul
      simpa using this
    exact this.symm

theorem exists_isFundamentalDomain_of_isCompact [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {C : Set G} (hC : IsCompact C)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ C) :
    ∃ 𝓕 L : Set G, MeasurableSet 𝓕 ∧ IsCompact L ∧ 𝓕 ⊆ L ∧ ∀ x, ∃! γ : Γ, γ • x ∈ 𝓕 := by
  classical
  choose V hVo hcV hVL hVinj using exists_isOpen_small Γ
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hVo (fun c _ => mem_iUnion.mpr ⟨c, hcV c⟩)
  let l := t.toList
  let A : ℕ → Set G := fun i => if h : i < l.length then V (l.get ⟨i, h⟩) else ∅
  have hAo : ∀ i, IsOpen (A i) := fun i => by
    simp only [A]; split_ifs
    · exact hVo _
    · exact isOpen_empty
  have hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1 := by
    intro i γ hγ x hx hγx
    simp only [A] at hx hγx
    split_ifs at hx hγx with h
    · exact hVinj _ γ hγ x hx hγx
    · exact hx.elim
  have hcovA : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i := by
    intro x
    obtain ⟨γ, hγ, hγC⟩ := hcov x
    obtain ⟨c, hc⟩ := mem_iUnion.mp (ht hγC)
    obtain ⟨hct, hcV'⟩ := mem_iUnion.mp hc
    obtain ⟨n, hn, hnc⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hct)
    refine ⟨n, γ, hγ, ?_⟩
    show γ * x ∈ (if h : n < l.length then V (l.get ⟨n, h⟩) else ∅)
    rw [dif_pos hn]
    have hget : l.get ⟨n, hn⟩ = c := hnc
    rw [hget]
    exact hcV'
  choose L hL hVL' using hVL
  refine ⟨firstHit Γ A, ⋃ c ∈ t, L c, measurableSet_firstHit Γ hAo,
    t.isCompact_biUnion fun c _ => hL c, ?_, existsUnique_mem_firstHit Γ A hinj hcovA⟩
  intro y hy
  obtain ⟨i, hi, -⟩ := mem_iUnion.mp hy
  simp only [A] at hi
  split_ifs at hi with h
  · exact mem_iUnion₂.mpr ⟨l.get ⟨i, h⟩, Finset.mem_toList.mp (List.get_mem l _), hVL' _ hi⟩
  · exact hi.elim

end GroundTheory.Heights₂.Theta
