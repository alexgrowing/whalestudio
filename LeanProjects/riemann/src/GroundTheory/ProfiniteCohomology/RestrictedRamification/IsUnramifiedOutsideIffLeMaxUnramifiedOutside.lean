import Mathlib
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Unramified
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

section Basic

variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem le_maxUnramifiedOutside {E : IntermediateField F Ω} [FiniteDimensional F E]
    (hE : IsUnramifiedOutside S E) : E ≤ maxUnramifiedOutside F Ω S :=
  le_iSup_of_le E (le_iSup_of_le ‹_› (le_iSup_of_le hE le_rfl))

theorem maxUnramifiedOutside_mono {S T : Set (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    maxUnramifiedOutside F Ω S ≤ maxUnramifiedOutside F Ω T :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_le fun hE =>
    le_iSup_of_le (fun v hv => hE v fun hs => hv (h hs)) le_rfl

theorem maxUnramifiedOutside_eq_iSup :
    maxUnramifiedOutside F Ω S =
      ⨆ E : {E : IntermediateField F Ω // FiniteDimensional F E ∧ IsUnramifiedOutside S E}, E.1 := by
  apply le_antisymm
  · exact iSup_le fun E => iSup_le fun hf => iSup_le fun hu => le_iSup_of_le ⟨E, hf, hu⟩ le_rfl
  · exact iSup_le fun E => have := E.2.1; le_maxUnramifiedOutside S E.2.2

variable [NumberField F] [IsGalois F Ω]

theorem mem_maxUnramifiedOutside_iff {x : Ω} :
    x ∈ maxUnramifiedOutside F Ω S ↔
      ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧ x ∈ E := by
  constructor
  · intro hx
    have hne : Nonempty {E : IntermediateField F Ω // FiniteDimensional F E ∧
        IsUnramifiedOutside S E} := ⟨⟨⊥, inferInstance, isUnramifiedOutside_bot S⟩⟩
    have hdir : Directed (· ≤ ·) (fun E : {E : IntermediateField F Ω // FiniteDimensional F E ∧
        IsUnramifiedOutside S E} => E.1) := by
      intro E₁ E₂
      have := E₁.2.1
      have := E₂.2.1
      exact ⟨⟨E₁.1 ⊔ E₂.1, inferInstance, E₁.2.2.sup E₂.2.2⟩, le_sup_left, le_sup_right⟩
    rw [maxUnramifiedOutside_eq_iSup, ← SetLike.mem_coe,
      IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
    obtain ⟨E, hE⟩ := hx
    exact ⟨E.1, E.2.1, E.2.2, hE⟩
  · rintro ⟨E, hf, hu, hx⟩
    exact le_maxUnramifiedOutside S hu hx

theorem exists_subset_of_subset_maxUnramifiedOutside (s : Finset Ω)
    (hs : ∀ x ∈ s, x ∈ maxUnramifiedOutside F Ω S) :
    ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
      ∀ x ∈ s, x ∈ E := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, isUnramifiedOutside_bot S, by simp⟩
  | insert a s _ ih =>
    obtain ⟨E₁, hf₁, hu₁, ha⟩ :=
      (mem_maxUnramifiedOutside_iff S).1 (hs a (Finset.mem_insert_self a s))
    obtain ⟨E₂, hf₂, hu₂, hs₂⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    refine ⟨E₁ ⊔ E₂, inferInstance, hu₁.sup hu₂, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact le_sup_left (α := IntermediateField F Ω) ha
    · exact le_sup_right (α := IntermediateField F Ω) (hs₂ x hx)

theorem isUnramifiedOutside_iff_le_maxUnramifiedOutside {E : IntermediateField F Ω}
    [FiniteDimensional F E] : IsUnramifiedOutside S E ↔ E ≤ maxUnramifiedOutside F Ω S := by
  refine ⟨le_maxUnramifiedOutside S, fun h => ?_⟩
  classical
  let b := Module.finBasis F E
  obtain ⟨E', hf, hu, hE'⟩ := exists_subset_of_subset_maxUnramifiedOutside S
    (Finset.univ.image fun i => (b i : Ω)) fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact h (b i).2
  have hle : E ≤ E' := by
    intro x hx
    have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
      have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
      rw [map_sum] at this
      simp only [map_smul] at this
      exact this.symm
    rw [hx']
    exact sum_mem fun i _ => E'.smul_mem (hE' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  exact fun v hv => isUnramifiedIn_of_le hle v (hu v hv)

instance isGalois_maxUnramifiedOutside : IsGalois F (maxUnramifiedOutside F Ω S) := by
  have hN : Normal F (maxUnramifiedOutside F Ω S) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    intro τ x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    obtain ⟨E, hf, hu, hyE⟩ := (mem_maxUnramifiedOutside_iff S).1 hy
    have : FiniteDimensional F (E.map (τ : Ω →ₐ[F] Ω)) :=
      LinearEquiv.finiteDimensional (IntermediateField.equivMap E (τ : Ω →ₐ[F] Ω)).toLinearEquiv
    exact le_maxUnramifiedOutside S (hu.map τ) ((IntermediateField.mem_map _).2 ⟨y, hyE, rfl⟩)
  exact ⟨⟩

theorem galUnramifiedOutside_isProfinite :
    CompactSpace (galUnramifiedOutside F Ω S) ∧ T2Space (galUnramifiedOutside F Ω S) ∧
      TotallyDisconnectedSpace (galUnramifiedOutside F Ω S) :=
  galois_isProfinite F (maxUnramifiedOutside F Ω S)

end Basic

section Relative

variable [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))

theorem isUnramifiedOutside_restrictScalars_iff {L : IntermediateField F Ω} [FiniteDimensional F L]
    (hL : IsUnramifiedOutside S L) (M : IntermediateField L Ω) [FiniteDimensional L M] :
    IsUnramifiedOutside S (M.restrictScalars F) ↔ IsUnramifiedOutside (placesOver S) M := by
  have := NumberField.of_module_finite F L
  have : FiniteDimensional F M := FiniteDimensional.trans F L M
  have := NumberField.of_module_finite L M
  change (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) ↔ _
  constructor
  · intro hM w hw Q hQ hQw
    have hv0 : w.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) w.ne_bot
    let v : HeightOneSpectrum (𝓞 F) := ⟨w.asIdeal.under (𝓞 F), inferInstance, hv0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have hv : v ∉ S := fun hvS => hw ⟨v, hvS, hwv⟩
    have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q w.asIdeal v.asIdeal
    exact ((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hM v hv Q hQ this)).2
  · intro hM v hv Q hQ hQv
    have hP0 : Q.under (𝓞 L) ≠ ⊥ := by
      have : (Q.under (𝓞 L)).LiesOver v.asIdeal :=
        ⟨by rw [Ideal.under_under]; exact hQv.over⟩
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot (Q.under (𝓞 L))
    let w : HeightOneSpectrum (𝓞 L) := ⟨Q.under (𝓞 L), inferInstance, hP0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by
      change v.asIdeal = (Q.under (𝓞 L)).under (𝓞 F)
      rw [Ideal.under_under]; exact hQv.over⟩
    have hw : w ∉ placesOver S := by
      rintro ⟨u, huS, hwu⟩
      have huv : u = v := HeightOneSpectrum.ext (hwu.over.trans hwv.over.symm)
      exact hv (huv ▸ huS)
    have h1 := hM w hw Q hQ ⟨rfl⟩
    have h2 := hL v hv (Q.under (𝓞 L)) inferInstance hwv
    exact (isUnramifiedAt_tower_iff (F := F) (L := L) Q).2 ⟨h2, h1⟩

variable [IsGalois F Ω]

theorem restrictScalars_maxUnramifiedOutside {L : IntermediateField F Ω} [FiniteDimensional F L]
    (hL : L ≤ maxUnramifiedOutside F Ω S) :
    (maxUnramifiedOutside L Ω (placesOver S)).restrictScalars F = maxUnramifiedOutside F Ω S := by
  have := NumberField.of_module_finite F L
  have hLu : IsUnramifiedOutside S L :=
    (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hL
  ext x
  rw [IntermediateField.mem_restrictScalars]
  constructor
  · intro hx
    obtain ⟨M, hf, hu, hxM⟩ := (mem_maxUnramifiedOutside_iff (placesOver S)).1 hx
    have : FiniteDimensional F (M.restrictScalars F) := FiniteDimensional.trans F L M
    exact le_maxUnramifiedOutside S
      ((isUnramifiedOutside_restrictScalars_iff S hLu M).2 hu) hxM
  · intro hx
    obtain ⟨E, hf, hu, hxE⟩ := (mem_maxUnramifiedOutside_iff S).1 hx
    let M : IntermediateField L Ω := IntermediateField.extendScalars (le_sup_left : L ≤ L ⊔ E)
    have : FiniteDimensional F M := (inferInstance : FiniteDimensional F ↥(L ⊔ E))
    have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
    have hMu : IsUnramifiedOutside S (M.restrictScalars F) := hLu.sup hu
    exact le_maxUnramifiedOutside (placesOver S)
      ((isUnramifiedOutside_restrictScalars_iff S hLu M).1 hMu)
      (le_sup_right (α := IntermediateField F Ω) hxE)

end Relative

end GroundTheory.ProfCoh
