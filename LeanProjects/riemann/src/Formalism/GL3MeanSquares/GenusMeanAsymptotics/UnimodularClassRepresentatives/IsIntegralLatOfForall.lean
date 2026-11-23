import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralAtLocF

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms SplitBAux

theorem gmap_inj (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B :=
  (gmap_injective g).eq_iff

theorem fibLoc_gmap (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T) = fibLoc S L 𝔭 T := by
  have hG : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := extOf_mem_isom hs S hg'
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap (extOf S g')
      invFun := Formalism.HermitianLatticesTheory.gmap (extOf S g').symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm (extOf S g').symm Λ }
  unfold fibLoc
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ (locF 𝔭 (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) ∧
    S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T))
  rw [← LocalizedFibreSets.gmap_locF, gmap_inj, StabilizerLattices.cut_gmap_extOf, ← LocalizedFibreSets.gmap_locF, gmap_inj,
    Formalism.HermitianLatticesTheory.isomAct_mem_gmap, symm_fix (extOf_x₀ S g')]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨extOf S g' * g, Subgroup.mul_mem _ hG hg, autSub_gmap_mul _ _ _⟩
  · rintro ⟨g, hg, e1⟩
    refine ⟨(extOf S g')⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hG) hg, ?_⟩
    rw [autSub_gmap_mul, e1, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem fibLoc_eq_of_rel (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} {M M₁ : Submodule (𝓞 K) V'}
    (H : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) = locF 𝔭 M₁) :
    fibLoc S L 𝔭 M₁ = fibLoc S L 𝔭 M := by
  obtain ⟨g, hg, e⟩ := H
  rw [← fibLoc_locF S L 𝔭 M₁, ← e, fibLoc_gmap hs S L 𝔭 hg, fibLoc_locF]

theorem sameGenus_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.SameGenus h A B ↔ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 A) = locF 𝔭.1 B := by
  constructor
  · rintro H ⟨𝔭, h𝔭⟩
    obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact H P hP
  · intro H P hP
    have hm : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have := H ⟨_, hm⟩
    rwa [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP] at this

theorem isIntegralLat_of_forall {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {M : Submodule (𝓞 K) W}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, IsIntegralAt 𝔭.1 h₀ (locF 𝔭.1 M)) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h₀ M := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  exact fun 𝔭 => H 𝔭 x (LocF.le_locF _ _ hx) y (LocF.le_locF _ _ hy)

theorem isIntegralAt_gmap {𝔭 : Ideal (𝓞 F)} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    {T : Submodule (𝓞 K) V} (hT : IsIntegralAt 𝔭 h T) : IsIntegralAt 𝔭 h (Formalism.HermitianLatticesTheory.gmap g T) := by
  intro x hx y hy
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hx hy
  rw [← isom_apply (symm_mem_isom hg)]
  exact hT _ hx _ hy

theorem tprod_natCast_ne_zero {ι : Type*} (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) :
    (∏' i, (f i : ℝ)) ≠ 0 := by
  by_cases hm : Multipliable fun i => (f i : ℝ)
  · have h1 : (1 : ℝ) ≤ ∏' i, (f i : ℝ) := by
      refine ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall fun s => ?_)
      have : (1 : ℝ) ≤ ((∏ i ∈ s, f i : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hf i)
      simpa using this
    linarith
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero

def Good (F : Type) [Field F] [NumberField F] [Algebra F K] (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (M : Submodule (𝓞 K) V') : Prop :=
  Submodule.IsLattice K M ∧ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 M ≠ 0

theorem Good.integral (hF : IsFixF K F) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : Formalism.HermitianLatticesTheory.IsIntegralLat h' M := by
  apply isIntegralLat_of_forall (F := F)
  intro 𝔭
  obtain ⟨C, -, hCi, e⟩ := exists_lattice_of_fibLoc_ne_zero S hL hLi (hM.2 𝔭)
  rw [← e]
  exact isIntegralAt_locF 𝔭.2.isPrime hF hCi

theorem Good.nonempty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : (fibG S L M).Nonempty := by
  have h1 := card_fibG_eq_prod (F := F) hK hF hs hd S hL hLi hM.1
  have h2 := tprod_natCast_ne_zero _ hM.2
  rw [← h1] at h2
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  apply h2
  rw [hne]
  simp

theorem Good.of_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    {S : VecSplit h h'} {L : Submodule (𝓞 K) V} {M M₁ : Submodule (𝓞 K) V'}
    (hM : Good F S L M) (h1 : M₁ ∈ Formalism.HermitianLatticesTheory.genus h' M) : Good F S L M₁ :=
  ⟨h1.1, fun 𝔭 => by
    rw [fibLoc_eq_of_rel hs S L ((sameGenus_iff hK hF M M₁).mp h1.2 𝔭)]
    exact hM.2 𝔭⟩

theorem exists_patch (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (τ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V')
    (hτ : ∀ 𝔭 ∈ Z, locF 𝔭.1 (τ 𝔭) = τ 𝔭 ∧ fibLoc S L 𝔭.1 (τ 𝔭) ≠ 0)
    (hZ : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A ≠ 0) :
    ∃ M, Good F S L M ∧ (∀ 𝔭 ∈ Z, locF 𝔭.1 M = τ 𝔭) ∧ ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
  obtain ⟨M, ⟨hMl, h1, h2⟩, -⟩ := exists_unique_patch hK hF hA Z τ (fun 𝔭 h𝔭 => by
    obtain ⟨C, hC, -, e⟩ := exists_lattice_of_fibLoc_ne_zero S hL hLi (hτ 𝔭 h𝔭).2
    exact ⟨(hτ 𝔭 h𝔭).1, C, hC, by rw [e, (hτ 𝔭 h𝔭).1]⟩)
  refine ⟨M, ⟨hMl, fun 𝔭 => ?_⟩, h1, h2⟩
  by_cases h𝔭 : 𝔭 ∈ Z
  · rw [fibLoc_congr S L (T' := τ 𝔭) (by rw [h1 𝔭 h𝔭, (hτ 𝔭 h𝔭).1])]
    exact (hτ 𝔭 h𝔭).2
  · rw [fibLoc_congr S L (h2 𝔭 h𝔭)]
    exact hZ 𝔭 h𝔭

open scoped Formalism.HermitianLattices.Ext.L3.StabilizerLattices in
theorem exists_locReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₀ : Submodule (𝓞 K) V'} (hM₀ : Good F S L M₀) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ s, IsLocReps S L 𝔭.1 s := by
  classical
  obtain ⟨s', hs'⟩ := exists_fibReps hK hs hd S hL hLi
  let A : Set (Submodule (𝓞 K) V') :=
    {T | locF 𝔭.1 T = T ∧ IsIntegralAt 𝔭.1 h' T ∧ fibLoc S L 𝔭.1 T ≠ 0}
  have hA : ∀ g : Formalism.HermitianLatticesTheory.isom h', ∀ T ∈ A, g • T ∈ A := by
    rintro g T ⟨h1, h2, h3⟩
    refine ⟨?_, isIntegralAt_gmap g.2 h2, ?_⟩
    · change locF 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) = Formalism.HermitianLatticesTheory.gmap g.1 T
      rw [← LocalizedFibreSets.gmap_locF, h1]
    · change fibLoc S L 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) ≠ 0
      rwa [fibLoc_gmap hs S L 𝔭.1 g.2]
  obtain ⟨s, hs1, hs2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h') A hA
    {T | T ∈ A ∧ T ∈ s'.image (locF 𝔭.1)}
    ((s'.image (locF 𝔭.1)).finite_toSet.subset fun T hT => hT.2) (fun c hc => hc.1) (by
      intro T hT
      obtain ⟨M, hM, h1, -⟩ := exists_patch hK hF S hL hLi hM₀.1 {𝔭} (fun _ => T)
        (fun 𝔮 h𝔮 => by
          rw [Finset.mem_singleton] at h𝔮
          subst h𝔮
          exact ⟨hT.1, hT.2.2⟩) (fun 𝔮 _ => hM₀.2 𝔮)
      obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, -⟩ := hs'.2 M (hM.nonempty hK hF hs hd hL hLi)
      have e2 : (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h') • locF 𝔭.1 Λ₀ = T := by
        change Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 Λ₀) = T
        rw [LocalizedFibreSets.gmap_locF, e, h1 𝔭 (Finset.mem_singleton_self _)]
      refine ⟨locF 𝔭.1 Λ₀, ⟨?_, Finset.mem_image_of_mem _ hΛ₀⟩, ⟨g, hg⟩, e2⟩
      have := hA (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h')⁻¹ T hT
      rwa [← e2, inv_smul_smul] at this)
  refine ⟨s, hs1, fun T h1 h2 h3 => ?_⟩
  obtain ⟨T₀, ⟨hT₀, g, hg⟩, hu⟩ := hs2 T ⟨h1, h2, h3⟩
  exact ⟨T₀, ⟨hT₀, g.1, g.2, hg⟩, fun T₁ ⟨h4, g₁, hg₁, e₁⟩ => hu T₁ ⟨h4, ⟨g₁, hg₁⟩, e₁⟩⟩

theorem isClassReps_filter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M)
    [DecidablePred fun Λ' : Submodule (𝓞 K) V' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'] :
    Formalism.ThetaLiftIndependence.IsClassReps h' M (s'.filter fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ') := by
  obtain ⟨he, hi, -⟩ :=
    Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V' h' (S.isSymm hs) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  constructor
  · intro Λ' hΛ'
    rw [Finset.mem_filter] at hΛ'
    obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'.1
    exact ⟨StabilizerLattices.isLattice_cut S hΛ.1, hΛ'.2⟩
  · intro M₁ hM₁
    obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, hu⟩ :=
      hs'.2 M₁ ((hM.of_genus hK hF hs hM₁).nonempty hK hF hs hd hL hLi)
    refine ⟨Λ₀, ⟨Finset.mem_filter.mpr ⟨hΛ₀, ?_⟩, g, hg, e⟩, ?_⟩
    · have h1 := hi Λ₀ g hg
      rw [e] at h1
      exact he.trans hM₁.2 (he.symm h1)
    · rintro Λ₁ ⟨h1, h2⟩
      exact hu Λ₁ ⟨(Finset.mem_filter.mp h1).1, h2⟩

end Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits
