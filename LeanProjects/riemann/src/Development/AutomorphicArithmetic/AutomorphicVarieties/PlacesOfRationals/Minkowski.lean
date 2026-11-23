import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Kum UpperTheory.V.B3

open CompanionTheory.PlaceDict in
private theorem exists_over {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [Algebra.IsAlgebraic E Ω] (L : IntermediateField E Ω) [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ A : ValuationSubring Ω, (cen A).IsMaximal ∧ (cen A).under (𝓞 L) = w.asIdeal := by
  have : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have := w.isMaximal
  obtain ⟨Q, hQ, hw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]
    exact bot_le)
  obtain ⟨A, rfl⟩ := exists_cen Q
  exact ⟨A, hQ, hw⟩

open CompanionTheory.PlaceDict in
private theorem lift_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L) (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[E] L)) :
    ∃ (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), AlgEquiv.restrictNormalHom L φ = τ ∧ φ ∈ Ine (F := E) A := by
  obtain ⟨A, hm, hw⟩ := exists_over L w
  obtain ⟨φ, h1, h2⟩ := lift L (cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact (hw.ge (hτ x) :)
  obtain ⟨h3, h4⟩ := of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  exact ⟨A, φ, h1, h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩

open scoped nonZeroDivisors Pointwise in
private theorem finite_case (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
    (S : Subgroup (M ≃ₐ[ℚ] M))
    (h : ∀ P : Ideal (𝓞 M), P.IsMaximal → P.inertia (M ≃ₐ[ℚ] M) ≤ S) : S = ⊤ := by
  set F : IntermediateField ℚ M := IntermediateField.fixedField S with hF
  have h1 : Module.finrank ℚ F = 1 := by
    by_contra hne
    obtain ⟨Q, hQ, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hne
    apply hram
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 M)))
    have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P Q
    have hG : IsGaloisGroup S F M := IsGaloisGroup.subgroup (M ≃ₐ[ℚ] M) ℚ M S
    have hG' : IsGaloisGroup S (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing S _ _ F M
    have hG0 : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ M
    have e1 := Ideal.card_inertia_eq_ramificationIdxIn (G := S) Q P
    have e2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) (P.under ℤ) P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q P S] at e1
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[ℚ] M)] at e2
    have e3 : Nat.card (P.inertia S) = Nat.card (P.inertia (M ≃ₐ[ℚ] M)) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h P hPmax)).toEquiv]
      rfl
    have e4 : P.ramificationIdx ℤ = Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) :=
      Ideal.ramificationIdx_tower Q P
    have e5 : 0 < P.ramificationIdx (𝓞 F) := P.ramificationIdx_pos _
    rw [← Ideal.ramificationIdx_eq_one_iff]
    have e6 : Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) = 1 * P.ramificationIdx (𝓞 F) := by
      rw [← e4, ← e2, ← e3, e1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right e5 e6
  have h2 : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
  rw [← IntermediateField.fixingSubgroup_fixedField S, ← hF, h2, IntermediateField.fixingSubgroup_bot]

open IntermediateField in
private theorem general {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ (M : Type) [Field M] [NumberField M] [Algebra E M] [IsGalois E M] (S : Subgroup (M ≃ₐ[E] M)),
      (∀ P : Ideal (𝓞 M), P.IsMaximal → P.inertia (M ≃ₐ[E] M) ≤ S) → S = ⊤)
    (H : Subgroup (Ω ≃ₐ[E] Ω)) (hn : H.Normal) (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hI : ∀ A : ValuationSubring Ω, Ine (F := E) A ≤ H) : H = ⊤ := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hfix : (fixedField H).fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  generalize fixedField H = L at hfix
  subst hfix
  have : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite _).1 ho
  have : IsGalois E L := (InfiniteGalois.normal_iff_isGalois _).1 hn
  have : NumberField L := NumberField.of_module_finite E _
  have hb : (⊥ : Subgroup (L ≃ₐ[E] L)) = ⊤ := hE L ⊥ fun P hP τ hτ => by
    let w : HeightOneSpectrum (𝓞 L) := ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField L)⟩
    obtain ⟨A, φ, h1, h2⟩ := lift_ine L w τ hτ
    rw [Subgroup.mem_bot, ← h1, ← MonoidHom.mem_ker, restrictNormalHom_ker]
    exact hI A h2
  rw [eq_top_iff, ← restrictNormalHom_ker]
  intro g _
  rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, hb]
  trivial

theorem UpperTheory.V.B3.minkowski :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : Subgroup (G ℚ Ω)), N.Normal → IsOpen (N : Set (G ℚ Ω)) →
    (∀ B : ValuationSubring Ω, Ine (F := ℚ) B ≤ N) → N = ⊤ := by
  intro Ω _ _ _ N hn ho hI
  refine general (fun M _ _ inst hG S hS => ?_) N hn ho hI
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact finite_case M S hS
