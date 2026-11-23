import Mathlib
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finite_primeSpectrum_height_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {a : A} (ha : a ≠ 0) :
    {P : PrimeSpectrum A | a ∈ P.asIdeal ∧ P.asIdeal.height = 1}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro ⟨P, hP⟩ ⟨haP, h1⟩
  simp only at haP h1
  refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem _).mpr haP⟩, fun Q hQ hQP => ?_⟩
  have := hQ.1
  have haQ : a ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.2
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact haQ)
  have hQ1 : P.height ≤ Q.height := by
    rw [h1]
    exact Order.one_le_iff_ne_zero.mpr (fun h => hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h))
  exact (Ideal.eq_of_le_of_height_le (I := Q) hQP hQ1).ge

theorem exists_primeSpectrum_height_one_le {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {a : A} (ha : a ≠ 0) (P : PrimeSpectrum A) (hP : a ∈ P.asIdeal) :
    ∃ Q : PrimeSpectrum A, a ∈ Q.asIdeal ∧ Q.asIdeal.height = 1 ∧ Q ≤ P := by
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := P.asIdeal)
    ((Ideal.span_singleton_le_iff_mem _).mpr hP)
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
  have hQ0 : Q ≠ ⊥ := fun h => ha (by rw [h] at haQ; exact haQ)
  refine ⟨⟨Q, hQp⟩, haQ, le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ)
    (Order.one_le_iff_ne_zero.mpr (fun h => hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h))), hQP⟩

theorem ringKrullDim_stalk_fromSpec {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(Z, U)) :
    ringKrullDim (Z.presheaf.stalk (hU.fromSpec P)) = P.asIdeal.height := by
  have hmem : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  letI := TopCat.Presheaf.algebra_section_stalk Z.presheaf (U := U) ⟨hU.fromSpec P, hmem⟩
  have := hU.isLocalization_stalk' P hmem
  exact @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ P.asIdeal _ _ _ _ this

theorem fromSpec_notMem_basicOpen_iff {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (f : Γ(Z, ⊤)) (P : PrimeSpectrum Γ(Z, U)) :
    hU.fromSpec P ∉ Z.basicOpen f ↔
      Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f ∈ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  have h := hU.fromSpec_preimage_basicOpen (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)
  have h2 : hU.fromSpec P ∈ Z.basicOpen (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f) ↔
      Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f ∉ P.asIdeal := by
    rw [← PrimeSpectrum.mem_basicOpen, ← h]
    rfl
  rw [Scheme.basicOpen_res] at h2
  have h3 : hU.fromSpec P ∈ U ⊓ Z.basicOpen f ↔ hU.fromSpec P ∈ Z.basicOpen f :=
    ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
  rw [← h3, h2, not_not]

theorem finite_codim_one_zero_set_and_exists :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsNoetherian Z] (ϖ : Γ(Z, ⊤)), ϖ ≠ 0 →
      {x : Z | x ∉ Z.basicOpen ϖ ∧ ringKrullDim (Z.presheaf.stalk x) = 1}.Finite ∧
      ∀ y : Z, y ∉ Z.basicOpen ϖ →
        ∃ x : Z, x ∉ Z.basicOpen ϖ ∧ ringKrullDim (Z.presheaf.stalk x) = 1 ∧
          y ∈ closure {x} := by
  intro Z _ _ ϖ hϖ
  have hex : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := fun y => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨U, hU, hy⟩
  choose U hU hyU using hex
  have hne : ∀ y, Nonempty (U y) := fun y => ⟨⟨y, hyU y⟩⟩
  have hnoeth : ∀ y, IsNoetherianRing Γ(Z, U y) := fun y =>
    IsLocallyNoetherian.component_noetherian ⟨U y, hU y⟩
  have hres : ∀ y, Z.presheaf.map (homOfLE (le_top : U y ≤ ⊤)).op ϖ ≠ 0 := fun y h =>
    hϖ (map_injective_of_isIntegral Z (homOfLE (le_top : U y ≤ ⊤)) (h.trans (map_zero _).symm))
  constructor
  · obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Z => (U y : Set Z))
      (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
    refine (t.finite_toSet.biUnion (fun y _ =>
      (finite_primeSpectrum_height_one (hres y)).image (hU y).fromSpec)).subset ?_
    rintro x ⟨hx, hx1⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    rw [← (hU y).range_fromSpec] at hxy
    obtain ⟨P, rfl⟩ := hxy
    refine ⟨P, ⟨(fromSpec_notMem_basicOpen_iff (hU y) ϖ P).mp hx, ?_⟩, rfl⟩
    rw [ringKrullDim_stalk_fromSpec (hU y) P] at hx1
    exact_mod_cast hx1
  · intro y hy
    have hy' : y ∈ Set.range (hU y).fromSpec := by
      rw [(hU y).range_fromSpec]; exact hyU y
    obtain ⟨P, hP⟩ := hy'
    obtain ⟨Q, hQ, hQ1, hQP⟩ := exists_primeSpectrum_height_one_le (hres y) P
      ((fromSpec_notMem_basicOpen_iff (hU y) ϖ P).mp (by rw [hP]; exact hy))
    refine ⟨(hU y).fromSpec Q, (fromSpec_notMem_basicOpen_iff (hU y) ϖ Q).mpr hQ, ?_, ?_⟩
    · rw [ringKrullDim_stalk_fromSpec (hU y) Q, hQ1]; rfl
    · have := ((PrimeSpectrum.le_iff_specializes Q P).mp hQP).map (hU y).fromSpec.continuous
      rw [hP] at this
      exact specializes_iff_mem_closure.mp this

end GlobalTheory.CompanionTheory.Ar.Flat
