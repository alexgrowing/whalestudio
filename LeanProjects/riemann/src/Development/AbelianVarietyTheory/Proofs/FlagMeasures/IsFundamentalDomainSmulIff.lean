import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

section General

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
  [BorelSpace K] (Γ : Subgroup K) (μ : Measure K)

theorem measure_eq [Countable Γ] [μ.IsMulLeftInvariant] {s t : Set K}
    (hs : IsFundamentalDomain Γ s μ) (ht : IsFundamentalDomain Γ t μ) : μ s = μ t := hs.measure_eq ht

omit [IsTopologicalGroup K] [BorelSpace K] in

theorem measure_ne_zero [Countable Γ] [μ.IsHaarMeasure] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) : μ s ≠ 0 :=
  hs.measure_ne_zero (NeZero.ne μ)

theorem measure_le_of_cover [Countable Γ] [μ.IsMulLeftInvariant] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) {C : Set K}
    (hcov : ∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) : μ s ≤ μ C := by
  open Pointwise in
  calc μ s ≤ μ (⋃ g : Γ, g • toMeasurable μ C ∩ s) := by
          refine measure_mono fun m hm => ?_
          obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov m
          refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_, hm⟩
          exact ⟨k, subset_toMeasurable μ C hk, rfl⟩
      _ ≤ ∑' g : Γ, μ (g • toMeasurable μ C ∩ s) := measure_iUnion_le _
      _ = μ (toMeasurable μ C) := (hs.measure_eq_tsum _).symm
      _ = μ C := measure_toMeasurable C

omit [TopologicalSpace K] [IsTopologicalGroup K] [BorelSpace K] in

theorem isFundamentalDomain_smul_iff {c : NNReal} (hc : c ≠ 0) (s : Set K) :
    IsFundamentalDomain Γ s (c • μ) ↔ IsFundamentalDomain Γ s μ := by
  have hc' : (c : ENNReal) ≠ 0 := by exact_mod_cast hc
  constructor
  · intro h
    refine h.mono fun t ht => ?_
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left hc'
  · intro h
    refine h.mono fun t ht => ?_
    rw [Measure.smul_apply, ht, smul_zero]

private theorem exists_measurableSet_unique_smul_mem_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V)
    (hΓV : ∀ γ ∈ Γ, γ ∈ V → γ = 1) :
    ∃ s : Set G, MeasurableSet s ∧ ∀ x : G, ∃! g : Γ, g • x ∈ s := by
  classical

  obtain ⟨U, hUo, hU1, hUV⟩ := exists_open_nhds_one_split (hV.mem_nhds h1)
  let W : Set G := U ∩ (fun u => u⁻¹) ⁻¹' U
  have hWo : IsOpen W := hUo.inter (hUo.preimage continuous_inv)
  have hW1 : (1 : G) ∈ W := ⟨hU1, by simp only [Set.mem_preimage, inv_one]; exact hU1⟩
  have hWW : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ V := fun a ha b hb => hUV a ha.1 b⁻¹ hb.2

  let A : G → Set G := fun g => (fun x => x * g⁻¹) ⁻¹' W
  have hAo : ∀ g, IsOpen (A g) := fun g => hWo.preimage (continuous_mul_const _)
  have hcov : ⋃ g, A g = Set.univ := Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.2 ⟨x, by simp only [A, Set.mem_preimage, mul_inv_cancel]; exact hW1⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable A hAo
  have hmemT : ∀ x, ∃ g ∈ T, x ∈ A g := fun x => by
    have hx : x ∈ ⋃ g ∈ T, A g := by rw [hTU, hcov]; exact Set.mem_univ x
    obtain ⟨g, hg, hx'⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨g, hg, hx'⟩
  have hTne : T.Nonempty := by
    obtain ⟨g, hg, -⟩ := hmemT 1
    exact ⟨g, hg⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let B : ℕ → Set G := fun i => A (f i)
  have hBo : ∀ i, IsOpen (B i) := fun i => hAo _
  have hBcov : ∀ x, ∃ i, x ∈ B i := by
    intro x
    obtain ⟨g, hgT, hx⟩ := hmemT x
    rw [hf] at hgT
    obtain ⟨i, rfl⟩ := hgT
    exact ⟨i, hx⟩

  have hinj : ∀ i y (δ : Γ), y ∈ B i → δ • y ∈ B i → δ = 1 := by
    intro i y δ hy hδy
    have hm := hWW (δ • y * (f i)⁻¹) hδy (y * (f i)⁻¹) hy
    have he : δ • y * (f i)⁻¹ * (y * (f i)⁻¹)⁻¹ = (δ : G) := by
      simp only [Subgroup.smul_def, smul_eq_mul]
      group
    rw [he] at hm
    exact Subtype.ext (hΓV _ δ.2 hm)

  let E : ℕ → Set G := fun j => ⋃ γ : Γ, (fun x => γ • x) ⁻¹' B j
  have hEo : ∀ j, IsOpen (E j) := fun j => isOpen_iUnion fun γ => (hBo j).preimage
    (by simpa only [Subgroup.smul_def, smul_eq_mul] using continuous_const_mul (γ : G))
  have hE : ∀ j y, y ∈ E j ↔ ∃ δ : Γ, δ • y ∈ B j := fun j y => by
    simp only [E, Set.mem_iUnion, Set.mem_preimage]

  let s : Set G := ⋃ i, (B i \ ⋃ (j : ℕ) (_ : j < i), E j)
  have hs : ∀ y, y ∈ s ↔ ∃ i, y ∈ B i ∧ ∀ j < i, ∀ δ : Γ, δ • y ∉ B j := by
    intro y
    simp only [s, Set.mem_iUnion, Set.mem_sdiff, not_exists]
    constructor
    · rintro ⟨i, hi, hn⟩
      exact ⟨i, hi, fun j hj δ hδ => hn j hj ((hE j y).2 ⟨δ, hδ⟩)⟩
    · rintro ⟨i, hi, hn⟩
      refine ⟨i, hi, fun j hj hy => ?_⟩
      obtain ⟨δ, hδ⟩ := (hE j y).1 hy
      exact hn j hj δ hδ
  refine ⟨s, MeasurableSet.iUnion fun i => (hBo i).measurableSet.diff
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => hEo j).measurableSet, fun x => ?_⟩
  have hP : ∃ i, ∃ γ : Γ, γ • x ∈ B i := by
    obtain ⟨i, hi⟩ := hBcov x
    exact ⟨i, 1, by simpa only [one_smul] using hi⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  refine ⟨γ, (hs _).2 ⟨_, hγ, fun j hj δ hδ => Nat.find_min hP hj ⟨δ * γ, by rwa [mul_smul]⟩⟩,
    fun γ' hγ' => ?_⟩
  obtain ⟨i', hi', hmin'⟩ := (hs _).1 hγ'
  have hle : Nat.find hP ≤ i' := Nat.find_min' hP ⟨γ', hi'⟩
  have hge : i' ≤ Nat.find hP := by
    by_contra hlt
    exact hmin' _ (not_le.1 hlt) (γ * γ'⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hγ)
  rw [le_antisymm hge hle] at hi'
  have h1' := hinj _ (γ • x) (γ' * γ⁻¹) hγ (by rw [mul_smul, inv_smul_smul]; exact hi')
  exact mul_inv_eq_one.1 h1'

end General

theorem countable_and_exists_domain (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) :
    IsTopologicalGroup K ∧ BorelSpace K ∧
    Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) ∧
    ∀ μ : Measure K, ∃ 𝓕 : Set K,
      IsFundamentalDomain (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) 𝓕 μ := by
  obtain ⟨hc, hd, -⟩ := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ n J
  change Countable (HFinIn (AF F) σ J) at hc
  change DiscreteTopology (HFinIn (AF F) σ J) at hd

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set (HFinIn (AF F) σ J)))
  have ht1 : (1 : HA (AF F) σ J) ∈ t := by
    have h : (1 : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := by rw [hteq]; exact Set.mem_singleton _
    exact h
  have htone : ∀ h ∈ HFinIn (AF F) σ J, h ∈ t → h = 1 := by
    intro h hh hht
    have h' : (⟨h, hh⟩ : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := hht
    rw [hteq] at h'
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h')
  have hcnt : Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) := by
    refine Function.Injective.countable
      (f := fun x => (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_subgroupOf.1 x.2⟩ :
        HFinIn (AF F) σ J)) ?_
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h2)

  have : SecondCountableTopology (AF F) := AdelicUnitaryTop.secondCountable_adele F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' (AF F) (AF F ⊗[F] E)
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hφ
  have : SecondCountableTopology (AF F ⊗[F] E) :=
    hq.isQuotientMap.secondCountableTopology hq.isOpenMap
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AF F ⊗[F] E)) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : SecondCountableTopology (HA (AF F) σ J) :=
    (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : HR (AF F) σ J → GL (Fin n) (AF F ⊗[F] E))).secondCountableTopology
  have : IsTopologicalGroup (HA (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  refine ⟨inferInstance, inferInstance, hcnt, fun μ => ?_⟩
  have hK1 : IsTopologicalGroup K := inferInstance
  have hK2 : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hK3 : OpensMeasurableSpace K := inferInstance
  obtain ⟨s, hs, hex⟩ := @exists_measurableSet_unique_smul_mem_of_discrete K _ _ hK1 hK2 _ hK3
    (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    ((Subtype.val : K → HA (AF F) σ J) ⁻¹' t) (ht.preimage continuous_subtype_val) ht1
    (fun γ hγ hγV => Subtype.ext (htone _ (Subgroup.mem_subgroupOf.1 hγ) hγV))
  exact ⟨s, IsFundamentalDomain.mk' hs.nullMeasurableSet hex⟩

theorem domains_and_covolume (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) (Γ : Subgroup K)
    (hΓ : Γ = Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    (cov : Measure K → ℝ)
    (hcov : ∀ ν : Measure K, (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν) →
      ∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν ∧ cov ν = (ν 𝓕).toReal)
    (μ : Measure K) (hμ : μ.IsHaarMeasure) :
    (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ) ∧
    (∀ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ → cov μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧
      ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧
    ∀ c : NNReal, c ≠ 0 → cov (c • μ) = (c : ℝ) * cov μ := by
  obtain ⟨hTG, hB, hcnt, hex⟩ := countable_and_exists_domain F E σ n J K
  rw [← hΓ] at hcnt hex
  have := hμ
  refine ⟨hex μ, fun 𝓕 h𝓕 => ?_, fun c hc => ?_⟩
  · obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    refine ⟨?_, @GlobalTheory.ClosedSubgroupCovol.measure_ne_zero _ _ _ _ Γ μ hcnt _ _ h𝓕,
      fun C _ hC => @GlobalTheory.ClosedSubgroupCovol.measure_le_of_cover _ _ _ hTG _ hB Γ μ hcnt _ _ h𝓕 _ hC⟩
    rw [hcv, @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓕' h𝓕]
  · obtain ⟨𝓕, h𝓕⟩ := hex μ
    obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    obtain ⟨𝓖, h𝓖, hcv'⟩ := hcov (c • μ) ⟨𝓕, (isFundamentalDomain_smul_iff Γ μ hc 𝓕).2 h𝓕⟩
    have h𝓖μ := (isFundamentalDomain_smul_iff Γ μ hc 𝓖).1 h𝓖
    rw [hcv', hcv, Measure.smul_apply,
      @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓖μ h𝓕', ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory.ClosedSubgroupCovol
