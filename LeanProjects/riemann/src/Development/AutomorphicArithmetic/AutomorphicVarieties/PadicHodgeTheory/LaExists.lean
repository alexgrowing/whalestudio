import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegree
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
open Topology Pointwise

private theorem ext_dense {W D B : Type} [Group W] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [CompactSpace D] [T2Space D] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (C : Set B) (hC : IsCompact C) (hχ : ∀ σ, χ σ ∈ C)
    (h1 : ∀ V ∈ 𝓝 (1 : B), ∃ U ∈ 𝓝 (1 : D), ∀ σ, i σ ∈ U → χ σ ∈ V) :
    ∃! κ : D →* B, Continuous κ ∧ ∀ σ, κ (i σ) = χ σ := by
  let Γ : Subgroup (D × B) := (i.prod χ).range.topologicalClosure
  have hΓ : IsCompact (Γ : Set (D × B)) := by
    refine (isCompact_univ.prod hC).of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    refine closure_minimal ?_ (isCompact_univ.prod hC).isClosed
    rintro _ ⟨σ, rfl⟩
    exact ⟨trivial, hχ σ⟩
  haveI : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓ
  let p : Γ →* D := (MonoidHom.fst D B).comp Γ.subtype
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hmem : ∀ σ, (i σ, χ σ) ∈ Γ := fun σ => Subgroup.le_topologicalClosure _ ⟨σ, rfl⟩
  have hinj : Function.Injective p := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨d, k⟩, hk⟩ hd
    obtain rfl : d = 1 := hd
    by_contra hne
    have hk1 : (1 : B) ≠ k := by
      rintro rfl
      exact hne rfl
    obtain ⟨V, V', hV, hV', hVV⟩ := t2_separation_nhds hk1
    obtain ⟨U, hU, H⟩ := h1 V hV
    obtain ⟨_, ⟨h2, h3⟩, σ, rfl⟩ := mem_closure_iff_nhds.1 hk _ (prod_mem_nhds hU hV')
    exact Set.disjoint_left.1 hVV (H σ h2) h3
  have hsurj : Function.Surjective p := by
    have h2 : IsClosed (Set.range p) := (isCompact_range hp).isClosed
    have h3 : Set.range i ⊆ Set.range p := by
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨_, hmem σ⟩, rfl⟩
    intro d
    exact closure_minimal h3 h2 (hi d)
  let e : Γ ≃* D := MulEquiv.ofBijective p ⟨hinj, hsurj⟩
  have he : Continuous e.symm := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hp
  refine ⟨((MonoidHom.snd D B).comp Γ.subtype).comp e.symm.toMonoidHom,
    ⟨continuous_snd.comp (continuous_subtype_val.comp he), fun σ => ?_⟩, ?_⟩
  · have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show (e.symm (i σ)).1.2 = _
    rw [this]
  · rintro κ ⟨hκ, H⟩
    refine DFunLike.coe_injective (hi.equalizer hκ (continuous_snd.comp (continuous_subtype_val.comp he)) ?_)
    funext σ
    have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show κ (i σ) = (e.symm (i σ)).1.2
    rw [this, H]

private def ballSub (l : ℕ) [Fact l.Prime] (ε : ℝ) (hε : 0 < ε) : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l)‖ = 1 ∧ ‖(x : Qbar l) - 1‖ < ε}
  one_mem' := by simpa using hε
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    have e : ((x * y : (Qbar l)ˣ) : Qbar l) - 1 = x * (y - 1) + (x - 1) := by push_cast; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx')
    rwa [norm_mul, hx, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    have e : ((x⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((x : Qbar l)⁻¹ * (x - 1)) := by
      have := x.ne_zero
      push_cast; field_simp; ring
    rwa [e, norm_neg, norm_mul, norm_inv, hx, inv_one, one_mul]

private theorem exists_compact {l : ℕ} [Fact l.Prime] (u : (Qbar l)ˣ) (hu : ‖(u : Qbar l)‖ = 1) :
    ∃ C : Subgroup (Qbar l)ˣ, IsCompact (C : Set (Qbar l)ˣ) ∧ u ∈ C ∧ ∀ x ∈ C, ‖(x : Qbar l)‖ = 1 := by
  let L : IntermediateField ℚ_[l] (Qbar l) := IntermediateField.adjoin ℚ_[l] {(u : Qbar l)}
  haveI : FiniteDimensional ℚ_[l] L := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  let C : Subgroup (Qbar l)ˣ :=
    { carrier := {x | (x : Qbar l) ∈ L ∧ ‖(x : Qbar l)‖ = 1}
      one_mem' := ⟨by simpa using L.one_mem, by simp⟩
      mul_mem' := fun hx hy => ⟨L.mul_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
      inv_mem' := fun hx => ⟨by simpa using L.inv_mem hx.1, by simp [hx.2]⟩ }
  refine ⟨C, ?_, ⟨IntermediateField.mem_adjoin_simple_self _ _, hu⟩, fun x hx => hx.2⟩
  rw [Units.isEmbedding_val₀.isCompact_iff]
  haveI : FiniteDimensional ℚ_[l] L.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[l] L)
  haveI : ProperSpace L.toSubmodule := FiniteDimensional.proper ℚ_[l] _
  convert (isCompact_sphere (0 : L.toSubmodule) 1).image continuous_subtype_val using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1⟩, by simpa using hy.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : ‖(y : Qbar l)‖ = 1 := by simpa using hy
    have h0 : (y : Qbar l) ≠ 0 := fun h => by simp [h] at hy'
    exact ⟨Units.mk0 _ h0, ⟨y.2, hy'⟩, rfl⟩

theorem UpperTheory.V.Loc.laExists :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ, Continuous ξ → (∀ x, ‖(ξ x : Qbar l)‖ = 1) → ∃! κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous κ ∧ ∀ σ : Weil h, κ (Subgroup.inclusion (Weil_le_Dec h) σ) = ξ (a σ) := by
  intro _ F Ω _ _ _ _ _ l _ A w h a ha ξ hξ hn
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI := compactSpace_Ine (E := F) A
  let χ := ξ.comp a
  have hI : Continuous fun τ : Ine (F := F) A => χ (ineIncl h τ) := hξ.comp ha.cont
  obtain ⟨C, hC, huC, hC1⟩ := exists_compact (χ (frob h)) (hn _)
  refine ext_dense (Subgroup.inclusion (Weil_le_Dec h)) ?_ χ
    ((C : Set (Qbar l)ˣ) * Set.range fun τ : Ine (F := F) A => χ (ineIncl h τ))
    (hC.mul (isCompact_range hI)) (fun σ => ?_) fun V hV => ?_
  · have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h
      (Subgroup.inclusion (Weil_le_Dec h) (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (Subgroup.inclusion (Weil_le_Dec h) (frob h)) ⊔
        (Ine (F := F) A).subgroupOf (Dec (F := F) A) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
      refine sup_le ?_ fun σ hσ => ⟨⟨σ, Ine_le_Weil h hσ⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    intro d
    have h3 : d ∈ (⊤ : Subgroup (Dec (F := F) A)) := trivial
    rw [← h1] at h3
    exact closure_mono h2 h3
  · obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    refine ⟨χ (frob h) ^ deg σ, C.zpow_mem huC _, _, ⟨τ, rfl⟩, ?_⟩
    conv_rhs => rw [hτ, map_mul, map_zpow]
  · rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hV
    obtain ⟨V', hV', hVV⟩ := hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV'
    let H := ballSub l ε hε
    have hH : ∀ x ∈ H, x ∈ V := fun x hx => hVV (hεV (by simpa [dist_eq_norm] using hx.2))
    have hop : IsOpen {x : (Qbar l)ˣ | ‖(x : Qbar l) - 1‖ < ε} :=
      isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
    haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
    have hHC : IsOpen ((H.subgroupOf C : Subgroup C) : Set C) := by
      convert hop.preimage (continuous_subtype_val (p := (· ∈ C))) using 1
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨hC1 _ x.2, hx⟩⟩
    haveI := (H.subgroupOf C).quotient_finite_of_isOpen hHC
    obtain ⟨N, hN, -, hNH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf C)) ⟨_, huC⟩
    have hNH' : χ (frob h) ^ N ∈ H := hNH
    have hM := (hop.preimage hI).mem_nhds (x := 1) (by simpa using hε)
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hM
    obtain ⟨U, hU, hUM⟩ := hM
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
    have hEo : IsOpen (E.fixingSubgroup : Set (G F Ω)) := E.fixingSubgroup_isOpen
    haveI := E.fixingSubgroup.quotient_finite_of_isOpen hEo
    obtain ⟨m, hm, -, hmE⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) (frob h : G F Ω)
    obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg F Ω A w h (m * N) (Nat.mul_pos hm hN)
    have hζo : IsOpen (MulAction.stabilizer (G F Ω) ζ : Set (G F Ω)) := stabilizer_isOpen_of_isIntegral ζ
    refine ⟨_, continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((hEo.inter hζo).mem_nhds ⟨E.fixingSubgroup.one_mem, (MulAction.stabilizer (G F Ω) ζ).one_mem⟩), fun σ hσ => hH _ ?_⟩
    obtain ⟨k, hk⟩ := hζ σ hσ.2
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    have h1 : ((frob h ^ deg σ : Weil h) : G F Ω) ∈ E.fixingSubgroup := by
      rw [hk, Subgroup.coe_zpow, Nat.cast_mul, mul_assoc, zpow_mul, zpow_natCast]
      exact E.fixingSubgroup.zpow_mem hmE _
    have h2 : (τ : G F Ω) ∈ E.fixingSubgroup := by
      have h3 : (σ : G F Ω) ∈ E.fixingSubgroup := hσ.1
      rw [hτ, Subgroup.coe_mul] at h3
      exact (E.fixingSubgroup.mul_mem_cancel_left h1).1 h3
    rw [hτ, map_mul, map_zpow]
    refine H.mul_mem ?_ ⟨hn _, hUM (hEU h2)⟩
    rw [hk, Nat.cast_mul, mul_comm (m : ℤ), mul_assoc, zpow_mul, zpow_natCast]
    exact H.zpow_mem hNH' _
