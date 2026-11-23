import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_fundamentalDomain_mass_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G], ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ Γ hΓ _ _
  obtain ⟨hdisc, K, hK, hKc⟩ := hΓ
  have : DiscreteTopology Γ := hdisc
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set Γ))
  have hU0 : ∀ γ ∈ Γ, γ ∈ U → γ = 0 := by
    intro γ hγ hγU
    have h : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := hγU
    rw [hU] at h
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h)
  have hUn : U ∈ nhds (0 : G) := by
    have h : (0 : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := by rw [hU]; rfl
    exact hUo.mem_nhds h

  obtain ⟨V, hV, hVU⟩ := exists_nhds_zero_half hUn
  set V₀ := interior (V ∩ (fun x => -x) ⁻¹' V) with hV₀
  have hV₀o : IsOpen V₀ := isOpen_interior
  have hV₀0 : (0 : G) ∈ V₀ := by
    rw [hV₀, mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hV ?_
    exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)
  have hsub : ∀ a ∈ V₀, ∀ b ∈ V₀, a - b ∈ U := by
    intro a ha b hb
    have ha' := (interior_subset ha).1
    have hb' : -b ∈ V := (interior_subset hb).2
    rw [sub_eq_add_neg]
    exact hVU a ha' (-b) hb'

  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : G => (fun x => x - k) ⁻¹' V₀)
    (fun k => hV₀o.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using hV₀0⟩)
  set l := t.toList with hl
  let c : ℕ → G := fun n => l.getD n 0
  let W : ℕ → Set G := fun n => (fun x => x - c n) ⁻¹' V₀ ∩ K ∩ {_x | n < l.length}
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, (fun x => (γ : G) + x) ⁻¹' W n
  let F : Set G := ⋃ n, (W n ∩ ⋂ m, ⋂ (_ : m < n), (S m)ᶜ)
  have hWm : ∀ n, MeasurableSet (W n) := fun n =>
    ((hV₀o.preimage (continuous_id.sub continuous_const)).measurableSet.inter
      hK.isClosed.measurableSet).inter (MeasurableSet.const _)
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    MeasurableSet.iUnion fun γ => (hWm n).preimage (measurable_const_add _)
  have hFm : MeasurableSet F :=
    MeasurableSet.iUnion fun n => (hWm n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hSm m).compl)
  have hFK : F ⊆ K := by
    intro x hx
    obtain ⟨n, hn, -⟩ := Set.mem_iUnion.1 hx
    exact hn.1.2

  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ x, γ + x ∈ S n ↔ x ∈ S n := by
    intro n γ hγ x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨⟨(δ : G) + γ, Γ.add_mem δ.2 hγ⟩, by simpa [add_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      refine ⟨⟨(δ : G) - γ, Γ.sub_mem δ.2 hγ⟩, ?_⟩
      rw [show (δ : G) - γ + (γ + x) = δ + x by abel]
      exact hδ

  have hcov : ∀ y ∈ K, ∃ n, y ∈ W n := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hkl : k ∈ l := by rw [hl]; exact Finset.mem_toList.2 hk
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hkl
    refine ⟨n, ⟨?_, hy⟩, hn⟩
    have hc : c n = l[n] := List.getD_eq_getElem _ _ hn
    simpa [hc] using hyk
  have hex : ∀ x : G, ∃! γ : Γ, γ +ᵥ x ∈ F := by
    intro x
    have hne : ∃ n, x ∈ S n := by
      obtain ⟨γ, hγ, hγK⟩ := hKc x
      obtain ⟨n, hn⟩ := hcov _ hγK
      exact ⟨n, Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hn⟩⟩
    classical
    obtain ⟨δ, hδ⟩ := Set.mem_iUnion.1 (Nat.find_spec hne)
    have hδF : δ +ᵥ x ∈ F := by
      refine Set.mem_iUnion.2 ⟨Nat.find hne, hδ, ?_⟩
      simp only [Set.mem_iInter, Set.mem_compl_iff]
      intro m hm
      change ¬ ((δ : G) + x ∈ S m)
      rw [hSinv m δ δ.2 x]
      exact Nat.find_min hne hm
    refine ⟨δ, hδF, ?_⟩
    intro γ hγ
    change (γ : G) + x ∈ F at hγ
    have hγ' : (δ : G) + x ∈ F := hδF
    obtain ⟨n, hn, hnS⟩ := Set.mem_iUnion.1 hγ
    obtain ⟨n', hn', hnS'⟩ := Set.mem_iUnion.1 hγ'
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hnS hnS'
    have hxn : x ∈ S n := Set.mem_iUnion.2 ⟨γ, hn⟩
    have hxn' : x ∈ S n' := Set.mem_iUnion.2 ⟨δ, hn'⟩
    rcases lt_trichotomy n n' with h | rfl | h
    · exact absurd ((hSinv n δ δ.2 x).2 hxn) (hnS' n h)
    · have hd := hsub _ hn.1.1 _ hn'.1.1
      have hmem : (γ : G) - δ ∈ Γ := Γ.sub_mem γ.2 δ.2
      have h0 := hU0 _ hmem (by simpa [sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] using hd)
      exact Subtype.ext (sub_eq_zero.1 h0)
    · exact absurd ((hSinv n' γ γ.2 x).2 hxn') (hnS n' h)

  let μ₀ : Measure G := Measure.addHaar
  have hF₀ : IsAddFundamentalDomain Γ F μ₀ := IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex
  have h0 : μ₀ F ≠ 0 := hF₀.measure_ne_zero (NeZero.ne μ₀)
  have htop : μ₀ F ≠ ⊤ := ((measure_mono hFK).trans_lt hK.measure_lt_top).ne
  refine ⟨(μ₀ F)⁻¹ • μ₀, F, Measure.IsAddHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0),
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end GlobalTheory.CuspGeneric
