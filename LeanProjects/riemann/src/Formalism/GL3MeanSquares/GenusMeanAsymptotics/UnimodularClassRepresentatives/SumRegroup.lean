import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLatticeOfFibReps

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MassProductFormula

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits LocalFactorEquality

open Classical in

theorem sum_regroup (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0) (hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0)
    (hZA : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    (s : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Finset (Submodule (𝓞 K) V'))
    (hsr : ∀ 𝔭, IsLocReps S L 𝔭.1 (s 𝔭)) :
    ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1 := by
  have hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1 := fun 𝔭 h𝔭 =>
    fibLoc_eq_one hK hF hs hd S hL hLi hA hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)
  have hex : ∀ τ : ↥Z → Submodule (𝓞 K) V', τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) →
      ∃ M, Good F S L M ∧ (∀ 𝔭 : ↥Z, locF 𝔭.1.1 M = τ 𝔭) ∧
        ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
    intro τ hτ
    rw [Fintype.mem_piFinset] at hτ
    obtain ⟨M, hM, h1, h2⟩ := exists_patch hK hF S hL hLi hA Z
      (fun 𝔭 => if H : 𝔭 ∈ Z then τ ⟨𝔭, H⟩ else ⊥)
      (fun 𝔭 h𝔭 => by
        simp only [dif_pos h𝔭]
        exact ⟨((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).1, ((hsr 𝔭).1 _ (hτ ⟨𝔭, h𝔭⟩)).2.2⟩)
      (fun 𝔭 h𝔭 => by rw [hZ1 𝔭 h𝔭]; exact one_ne_zero)
    exact ⟨M, hM, fun 𝔭 => by rw [h1 𝔭.1 𝔭.2, dif_pos 𝔭.2], h2⟩
  choose! M hMg hMZ hMA using hex
  rw [← Finset.prod_coe_sort Z (fun 𝔭 => ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1),
    Finset.prod_univ_sum, Finset.mul_sum]
  have e1 : ∀ τ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1),
      c * ∏ 𝔭 : ↥Z, ((fibLoc S L 𝔭.1.1 (τ 𝔭) : ℝ) * lamP h' (τ 𝔭) 𝔭.1.1) =
        ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' (M τ) Λ'),
          (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
    intro τ hτ
    rw [sum_genus hK hF hs hd S hL hLi hc hs' hA hAi Z hZ1 hZA (hMg τ hτ) (hMA τ hτ),
      ← Finset.prod_coe_sort Z]
    congr 1
    refine Finset.prod_congr rfl fun 𝔭 _ => ?_
    rw [hMZ τ hτ 𝔭]
  rw [Finset.sum_congr rfl e1]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Λ' hΛ' => ?_
  by_cases hg : Good F S L Λ'
  · have hloc : ∀ 𝔭 : ↥Z, ∃! T₀, T₀ ∈ s 𝔭.1 ∧
        ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = locF 𝔭.1.1 Λ' := fun 𝔭 =>
      (hsr 𝔭.1).2 _ (LocF.locF_idem _ _)
        (isIntegralAt_locF 𝔭.1.2.isPrime hF (hg.integral hF hL hLi))
        (by rw [fibLoc_locF]; exact hg.2 𝔭.1)
    choose τ₀ hτ₀ hu using hloc
    have hmem : τ₀ ∈ Fintype.piFinset (fun 𝔭 : ↥Z => s 𝔭.1) :=
      Fintype.mem_piFinset.mpr fun 𝔭 => (hτ₀ 𝔭).1
    rw [Finset.sum_eq_single τ₀, if_pos]
    · rw [sameGenus_iff hK hF]
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ Z
      · have := (hτ₀ ⟨𝔭, h𝔭⟩).2
        rw [hMZ τ₀ hmem ⟨𝔭, h𝔭⟩]
        exact this
      · exact good_orbit hK hF hs hd S hL hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭)
          ((hMg τ₀ hmem).2 𝔭) (hg.2 𝔭)
    · intro τ hτ hne
      rw [if_neg]
      intro hsg
      apply hne
      funext 𝔭
      apply hu 𝔭
      refine ⟨Fintype.mem_piFinset.mp hτ 𝔭, ?_⟩
      have := (sameGenus_iff hK hF _ _).mp hsg 𝔭.1
      rwa [hMZ τ hτ 𝔭] at this
    · intro hc'
      exact absurd hmem hc'
  · have hlat := isLattice_of_fibReps S hs' hΛ'
    have : ∃ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 Λ' = 0 := by
      by_contra hcon
      push Not at hcon
      exact hg ⟨hlat, hcon⟩
    obtain ⟨𝔭, h𝔭⟩ := this
    rw [card_fibG_eq_zero hK hF hs hd S hL hLi hlat 𝔭 h𝔭]
    simp

theorem repMass_eq_prod_psi' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) =
      c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 := by
  classical
  obtain ⟨s', hs'⟩ := exists_fibReps hK hs hd S hL hLi
  rw [repMass_eq_sum_fib hK hs hd S hL hLi hs']
  by_cases H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∃ T, fibLoc S L 𝔭.1 T ≠ 0
  · obtain ⟨n, hn⟩ := exists_norm_eq hF hs S hLi H
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact S.hx₀ (by rw [hn]; simp)
    have hA := StabilizerLattices.isLattice_cut S hL
    have hAi := isIntegralLat_cut S hLi
    have f1 := finite_vd_ne_zero hK hF hs hd hL hLi
    have f2 := finite_vF_ne_zero hn0
    have f3 := finite_vd_ne_zero hK hF (S.isSymm hs) (S.isTotPosDef hd) hA hAi
    set Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
      f1.toFinset ∪ f2.toFinset ∪ f3.toFinset with hZ
    have hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inl h0))
    have hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (Or.inr h0))
    have hZA : ∀ 𝔭 ∉ Z, vd h' (S.cut L) 𝔭.1 = 0 := by
      intro 𝔭 h𝔭
      by_contra h0
      exact h𝔭 (by simp only [hZ, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inr h0)
    choose T hT using H
    obtain ⟨M₀, hM₀, -, -⟩ := exists_patch hK hF S hL hLi hA Z (fun 𝔭 => locF 𝔭.1 (T 𝔭))
      (fun 𝔭 _ => ⟨LocF.locF_idem _ _, by rw [fibLoc_locF]; exact hT 𝔭⟩)
      (fun 𝔭 h𝔭 => by
        rw [fibLoc_eq_one hK hF hs hd S hL hLi hA hAi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭) (hZA 𝔭 h𝔭)]
        exact one_ne_zero)
    have hex := fun 𝔭 => exists_locReps hK hF hs hd S hL hLi hM₀ 𝔭
    rw [sum_regroup hK hF hs hd S hL hLi hc hs' hn hA hAi Z hZL hZn hZA
      (fun 𝔭 => (hex 𝔭).choose) (fun 𝔭 => (hex 𝔭).choose_spec)]
    congr 1
    rw [tprod_eq_prod (s := Z) (fun 𝔭 h𝔭 =>
      psiP_eq_one' hK hF hs hd S hL hLi 𝔭.2 hn (hZL 𝔭 h𝔭) (hZn 𝔭 h𝔭))]
    exact Finset.prod_congr rfl fun 𝔭 _ => (psiP_eq S L 𝔭.1 (hex 𝔭)).symm
  · push Not at H
    obtain ⟨𝔭, H⟩ := H
    rw [tprod_of_exists_eq_zero ⟨𝔭, psiP_eq_zero S L 𝔭.1 H⟩, mul_zero]
    refine Finset.sum_eq_zero fun Λ' hΛ' => ?_
    rw [card_fibG_eq_zero hK hF hs hd S hL hLi (isLattice_of_fibReps S hs' hΛ') 𝔭 (H Λ')]
    simp

end Formalism.HermitianLattices.Ext.L3.MassProductFormula
