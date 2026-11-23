import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem locF_mem_fibSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {L Λ : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'} (hΛ : Λ ∈ fibG S L Λ') {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibSet S L 𝔭 Λ' := by
  obtain ⟨⟨-, hgen⟩, hx, hc⟩ := hΛ
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)
    | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 F) (𝓞 K)
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       have := congrArg (fun z : 𝓞 K => (z : K)) hab
       simpa using this)
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine ⟨locF_idem 𝔭 Λ, ?_, le_locF 𝔭 Λ hx, ?_⟩
  · obtain ⟨g, hg, e⟩ := hgen P hP
    refine ⟨g, hg, ?_⟩
    rw [← hPc, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact e
  · rw [cut_locF, hc]

theorem adjoin_le_of_mem_fibSet (S : VecSplit h h') {L Λ : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {𝔭 : Ideal (𝓞 F)} (hΛ : Λ ∈ fibSet S L 𝔭 Λ') : S.adjoin Λ' ≤ Λ := by
  obtain ⟨-, -, hx, hc⟩ := hΛ
  refine sup_le ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx
  · rw [Submodule.map_le_iff_le_comap]
    exact (LocF.le_locF 𝔭 Λ').trans hc.symm.le

private theorem star_algebraMap_of_fixed_field_eq (hF : IsFixF K F) (t : 𝓞 F) :
    star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
  rw [hF]
  refine ⟨(t : F), ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  first
  | rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]; rfl
  | simp

theorem adjoin_integral_of_nonempty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (fibSet S L 𝔭.1 Λ').Nonempty) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin Λ') := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  intro 𝔭
  obtain ⟨Λ, hΛ⟩ := H 𝔭
  have hle := adjoin_le_of_mem_fibSet S hΛ
  obtain ⟨-, ⟨g, hg, hgΛ⟩, -, -⟩ := hΛ
  have hp : 𝔭.1.IsPrime := 𝔭.2.isPrime
  rw [← hgΛ] at hle
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.1 (hle hx)
  obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 (hle hy)
  rw [LocF.mem_locF_iff hp] at hx' hy'
  rw [LocF.mem_locF_iff hp]
  obtain ⟨t, ht, htx⟩ := hx'
  obtain ⟨s, hs, hsy⟩ := hy'
  refine ⟨t * s, fun hts => (hp.mem_or_mem hts).elim ht hs, ?_⟩
  have key := hLi _ htx _ hsy
  have e1 : h (g x') (g y') = h x' y' := hg x' y'
  simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  rw [e1]
  rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x',
    ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s) y'] at key
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, starRingEnd_apply,
    star_algebraMap_of_fixed_field_eq hF] at key
  convert key using 1
  rw [Algebra.smul_def, map_mul, map_mul, smul_eq_mul, smul_eq_mul]
  simp only [RingHom.id_apply]
  ring

private theorem isLattice_gmap_of_isLattice (g : V ≃ₗ[K] V) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
  obtain ⟨hfg, hspan⟩ := hL
  refine ⟨hfg.map _, ?_⟩
  show Submodule.span K ((L.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) : Set V)) = ⊤
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan,
    Submodule.map_top, LinearEquiv.range]

private theorem comap_algebraMap_isMaximal_of_isMaximal (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := by
  haveI := hP
  first
  | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  | exact inferInstance
  | exact Ideal.IsMaximal.under (𝓞 F) P

theorem card_fibG_eq_card_pi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsLattice K Λ') (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hs1 : ∀ 𝔭 ∉ s, fibSet S L 𝔭.1 Λ' = {locF 𝔭.1 (S.adjoin Λ')}) :
    Nat.card (fibG S L Λ') = Nat.card (∀ 𝔭 : s, fibSet S L 𝔭.1.1 Λ') := by
  classical
  have hN : Submodule.IsLattice K (S.adjoin Λ') := (VecSplit.isLattice_adjoin_iff' (S := S) Λ').2 hΛ'
  have hsing : ∀ 𝔭 ∉ s, locF 𝔭.1 (S.adjoin Λ') ∈ fibSet S L 𝔭.1 Λ' := fun 𝔭 h𝔭 => by
    rw [hs1 𝔭 h𝔭]; rfl
  let Φ : fibG S L Λ' → ∀ 𝔭 : s, fibSet S L 𝔭.1.1 Λ' := fun Λ 𝔭 =>
    ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibSet hK hF S Λ.2 𝔭.1.2⟩
  have hloc : ∀ (Λ : fibG S L Λ') (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}), 𝔭 ∉ s →
      locF 𝔭.1 Λ.1 = locF 𝔭.1 (S.adjoin Λ') := by
    intro Λ 𝔭 h𝔭
    have := locF_mem_fibSet hK hF S Λ.2 𝔭.2
    rw [hs1 𝔭 h𝔭] at this
    exact this
  have hinj : Function.Injective Φ := by
    intro Λ₁ Λ₂ e
    apply Subtype.ext
    rw [← LocF.iInf_locF (F := F) Λ₁.1, ← LocF.iInf_locF (F := F) Λ₂.1]
    refine iInf_congr fun 𝔭 => ?_
    by_cases h𝔭 : 𝔭 ∈ s
    · exact congrArg (fun φ => (φ ⟨𝔭, h𝔭⟩).1) e
    · rw [hloc Λ₁ 𝔭 h𝔭, hloc Λ₂ 𝔭 h𝔭]
  have hsurj : Function.Surjective Φ := by
    intro f
    have hg : ∀ 𝔭 : s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1.1 L) = (f 𝔭).1 := by
      intro 𝔭
      obtain ⟨-, hex, -, -⟩ := (f 𝔭).2
      exact hex
    choose g hgi hgf using hg
    let B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V := fun 𝔭 =>
      if h𝔭 : 𝔭 ∈ s then Formalism.HermitianLatticesTheory.gmap (g ⟨𝔭, h𝔭⟩) L else S.adjoin Λ'
    have hBlat : ∀ 𝔭, Submodule.IsLattice K (B 𝔭) := by
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ s
      · simp only [B, dif_pos h𝔭]
        exact isLattice_gmap_of_isLattice _ hL
      · simp only [B, dif_neg h𝔭]
        exact hN
    have hBs : ∀ 𝔭 ∉ s, B 𝔭 = S.adjoin Λ' := fun 𝔭 h𝔭 => by simp only [B, dif_neg h𝔭]
    obtain ⟨hMlat, hMloc⟩ := LocF.patch hN s B hBlat hBs
    have hBf : ∀ 𝔭 (h𝔭 : 𝔭 ∈ s), locF 𝔭.1 (B 𝔭) = (f ⟨𝔭, h𝔭⟩).1 := by
      intro 𝔭 h𝔭
      simp only [B, dif_pos h𝔭]
      rw [← gmap_locF]
      exact hgf ⟨𝔭, h𝔭⟩
    have hBmem : ∀ 𝔭, locF 𝔭.1 (B 𝔭) ∈ fibSet S L 𝔭.1 Λ' := by
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ s
      · rw [hBf 𝔭 h𝔭]; exact (f ⟨𝔭, h𝔭⟩).2
      · rw [hBs 𝔭 h𝔭]; exact hsing 𝔭 h𝔭
    have hMmem : (⨅ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 (B 𝔭)) ∈ fibG S L Λ' := by
      refine ⟨⟨hMlat, ?_⟩, ?_, ?_⟩
      · intro P hP
        have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := comap_algebraMap_isMaximal_of_isMaximal P hP
        obtain ⟨-, ⟨g', hg', e'⟩, -, -⟩ := hBmem ⟨_, h𝔭⟩
        refine ⟨g', hg', ?_⟩
        rw [← locF_eq_loc hK hF hP, ← locF_eq_loc hK hF hP]
        rw [hMloc ⟨_, h𝔭⟩]
        exact e'
      · rw [Submodule.mem_iInf]
        intro 𝔭
        obtain ⟨-, -, hx, -⟩ := hBmem 𝔭
        exact hx
      · show Submodule.comap _ _ = Λ'
        rw [Submodule.comap_iInf]
        conv_rhs => rw [← LocF.iInf_locF (F := F) Λ']
        refine iInf_congr fun 𝔭 => ?_
        obtain ⟨-, -, -, hc⟩ := hBmem 𝔭
        exact hc
    refine ⟨⟨_, hMmem⟩, ?_⟩
    funext 𝔭
    apply Subtype.ext
    show locF 𝔭.1.1 (⨅ 𝔮 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔮.1 (B 𝔮)) = (f 𝔭).1
    rw [hMloc 𝔭.1]
    exact hBf 𝔭.1 𝔭.2
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
