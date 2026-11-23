import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem mem_asIdeal_iff_mem_span_of_above (l : ℕ) [hl : Fact l.Prime] (u : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hu : u ∈ Formalism.GaloisCohomology.Above ℚ l) (x : 𝓞 ℚ) :
    x ∈ u.asIdeal ↔ Rat.ringOfIntegersEquiv x ∈ Ideal.span {(l : ℤ)} := by
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
  have hP : Ideal.span {(l : ℤ)} = Ideal.comap (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) u.asIdeal := by
    refine hmax.eq_of_le (Ideal.comap_ne_top _ u.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (l : ℤ) = (l : 𝓞 ℚ) := map_natCast _ l
    rw [this]
    exact hu
  rw [hP, Ideal.mem_comap]
  have hx : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) = x :=
    RingEquiv.symm_apply_apply _ x
  rw [hx]

private theorem mt_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (A B : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (hB : B.valuation (l : Ω) < 1) :
    ∃ g : G ℚ Ω, ∀ x, g x ∈ A ↔ x ∈ B := by
  have hA0 : A ≠ ⊤ := fun h => ((UpperTheory.V.Base.places ℚ Ω l A).2.1 h).2 hA
  have hB0 : B ≠ ⊤ := fun h => ((UpperTheory.V.Base.places ℚ Ω l B).2.1 h).2 hB
  obtain ⟨v, hv⟩ := (UpperTheory.V.Base.places ℚ Ω l A).1 hA0
  obtain ⟨w, hw⟩ := (UpperTheory.V.Base.places ℚ Ω l B).1 hB0
  have hvl : v ∈ Formalism.GaloisCohomology.Above ℚ l := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.1 v hv).1 hA
  have hwl : w ∈ Formalism.GaloisCohomology.Above ℚ l := ((UpperTheory.V.Base.places ℚ Ω l B).2.2.1 w hw).1 hB
  have hvw : v = w := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext x
    rw [mem_asIdeal_iff_mem_span_of_above l v hvl x, mem_asIdeal_iff_mem_span_of_above l w hwl x]
  subst hvw
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hv hw
  refine ⟨σ.symm, fun x => ?_⟩
  rw [← hσ]
  show _ ↔ x ∈ Subring.map (MulSemiringAction.toRingHom (G ℚ Ω) Ω σ) A.toSubring
  rw [Subring.mem_map]
  constructor
  · intro hx
    exact ⟨σ.symm x, hx, by simp [MulSemiringAction.toRingHom_apply, AlgEquiv.smul_def]⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [MulSemiringAction.toRingHom_apply, AlgEquiv.smul_def] using ha

private theorem mt_not_both (L : Type) [Field L] [NumberField L] [IsTotallyReal L] [IsTotallyComplex L] : False := by
  obtain w : NumberField.InfinitePlace L := Classical.choice inferInstance
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) (IsTotallyReal.isReal w)

private theorem mt_cm {Ω : Type} [Field Ω] [CharZero Ω] (K F : IntermediateField ℚ Ω) [NumberField K] [NumberField F]
    [NumberField ↥(F ⊔ K)] [IsCMField K] [IsTotallyReal F] (hK : Module.finrank ℚ K = 2) : IsCMField ↥(F ⊔ K) := by
  letI : Algebra K ↥(F ⊔ K) := (IntermediateField.inclusion (le_sup_right : K ≤ F ⊔ K)).toRingHom.toAlgebra
  haveI : IsTotallyComplex ↥(F ⊔ K) := NumberField.isTotallyComplex_of_algebra K _
  letI : Algebra F ↥(F ⊔ K) := (IntermediateField.inclusion (le_sup_left : F ≤ F ⊔ K)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F ↥(F ⊔ K) := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Module.Free F ↥(F ⊔ K) := Module.Free.of_divisionRing F _
  haveI : Module.Finite F ↥(F ⊔ K) := Module.Finite.of_restrictScalars_finite ℚ F _
  have hle := IntermediateField.finrank_sup_le F K
  have hmul := Module.finrank_mul_finrank ℚ F ↥(F ⊔ K)
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hne : Module.finrank F ↥(F ⊔ K) ≠ 1 := by
    intro h1
    have hb := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1
    haveI : IsTotallyReal ↥(F ⊔ K) := IsTotallyReal.ofRingEquiv (RingEquiv.ofBijective (algebraMap F ↥(F ⊔ K)) hb)
    exact mt_not_both ↥(F ⊔ K)
  have hpos' : 0 < Module.finrank F ↥(F ⊔ K) := Module.finrank_pos
  haveI : Algebra.IsQuadraticExtension F ↥(F ⊔ K) := ⟨by
    rw [hK] at hle
    have : Module.finrank F ↥(F ⊔ K) ≤ 2 := by
      by_contra hc
      push_neg at hc
      have := Nat.mul_lt_mul_of_pos_left hc hpos
      omega
    omega⟩
  exact NumberField.IsCMField.ofCMExtension F ↥(F ⊔ K)

private theorem mt_out {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K F : IntermediateField ℚ Ω) [NumberField K]
    [NumberField F] [IsCMField K] [IsTotallyReal F] : ∃ h ∈ F.fixingSubgroup, h ∉ K.fixingSubgroup := by
  by_contra hcon
  push_neg at hcon
  have hle : F.fixingSubgroup ≤ K.fixingSubgroup := hcon
  have hKF : K ≤ F := by
    have h := IntermediateField.fixedField_le hle
    rwa [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at h
  letI : Algebra K F := (IntermediateField.inclusion hKF).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsTotallyReal K := IsTotallyReal.of_algebra K F
  exact mt_not_both K

private theorem mem_or_mul_mem_fixing_of_quadratic {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : IntermediateField ℚ Ω)
    [NumberField K] (hK : Module.finrank ℚ K = 2) (h τ : G ℚ Ω) (hh : h ∉ K.fixingSubgroup) :
    τ ∈ K.fixingSubgroup ∨ h * τ ∈ K.fixingSubgroup := by
  have hN : Normal ℚ K := by
    haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
    exact inferInstance
  have hG : IsGalois ℚ K := by
    haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
    exact inferInstance
  have hk := @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ K hN
  rw [← hk] at hh ⊢
  rw [MonoidHom.mem_ker] at hh
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul]
  by_cases ht : (@AlgEquiv.restrictNormalHom ℚ _ Ω _ _ K _ _ _ _ hN) τ = 1
  · exact Or.inl ht
  · right
    have hc0 : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
      haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
      rw [IsGalois.card_aut_eq_finrank ℚ K, hK]
    have hc : Nat.card (@AlgEquiv ℚ K K _ _ _ K.algebra' K.algebra') = 2 := by
      rw [← hc0]
      congr 1
      all_goals exact Subsingleton.elim _ _
    obtain ⟨y, hy, hu⟩ := (Nat.card_eq_two_iff' (1 : @AlgEquiv ℚ K K _ _ _ K.algebra' K.algebra')).mp hc
    by_contra hm
    have e1 := hu _ hh
    have e2 := hu _ ht
    have e3 := hu _ hm
    exact ht (mul_eq_left.mp (e3.trans e1.symm))

private theorem exists_conj_between_valuationSubrings_of_common {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) (A B C : ValuationSubring Ω)
    (g g' : G F Ω) (h1 : ∀ x, g x ∈ A ↔ x ∈ B) (h2 : ∀ x, g' x ∈ C ↔ x ∈ B) :
    ∃ k : G F Ω, ∀ x, k x ∈ A ↔ x ∈ C := by
  refine ⟨g * g'⁻¹, fun x => ?_⟩
  rw [AlgEquiv.mul_apply, h1, ← h2, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

private theorem inv_apply_mem_iff_of_apply_mem_iff {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) (A B : ValuationSubring Ω)
    (g : G F Ω) (h1 : ∀ x, g x ∈ A ↔ x ∈ B) : ∀ x, g⁻¹ x ∈ B ↔ x ∈ A := by
  intro x
  rw [← h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

private theorem exists_conj_valuationSubrings_trans {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) (A B C : ValuationSubring Ω)
    (g g' : G F Ω) (h1 : ∀ x, g x ∈ A ↔ x ∈ B) (h2 : ∀ x, g' x ∈ B ↔ x ∈ C) :
    ∃ k : G F Ω, ∀ x, k x ∈ A ↔ x ∈ C := by
  refine ⟨g * g', fun x => ?_⟩
  rw [AlgEquiv.mul_apply, h1, h2]

private theorem exists_over_l_place_conj_agreeing_on_field {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (K F : IntermediateField ℚ Ω) [NumberField K] (hK : Module.finrank ℚ K = 2)
    (h : G ℚ Ω) (hhF : h ∈ F.fixingSubgroup) (hhK : h ∉ K.fixingSubgroup)
    (P A : ValuationSubring Ω) (hP : P.valuation (l : Ω) < 1) (hA : A.valuation (l : Ω) < 1) :
    ∃ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 ∧ (∀ x ∈ K, x ∈ B ↔ x ∈ P) ∧
      ∃ g : G F Ω, ∀ x, g x ∈ A ↔ x ∈ B := by
  obtain ⟨σ, hσ⟩ := mt_conj l A P hA hP
  obtain ⟨m, hmF, hmK⟩ : ∃ m ∈ F.fixingSubgroup, ∀ x ∈ K, m x = σ x := by
    have hh' : h⁻¹ ∉ K.fixingSubgroup := fun hc => hhK (by simpa using K.fixingSubgroup.inv_mem hc)
    rcases mem_or_mul_mem_fixing_of_quadratic K hK h⁻¹ σ hh' with hs | hs
    · refine ⟨1, F.fixingSubgroup.one_mem, fun x hx => ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      rw [hs x hx]
      rfl
    · refine ⟨h, hhF, fun x hx => ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      have e := hs x hx
      rw [AlgEquiv.mul_apply] at e
      calc h x = h (h⁻¹ (σ x)) := by rw [e]
        _ = σ x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  let gm : G F Ω := IntermediateField.fixingSubgroupEquiv F ⟨m, hmF⟩
  refine ⟨A.comap (gm : Ω →+* Ω), ?_, ?_, gm, fun x => ?_⟩
  · have key := UpperTheory.V.val_lt_one (σ := gm.toRingEquiv) (A := A.comap (gm : Ω →+* Ω)) (A' := A)
      (fun x => by rw [ValuationSubring.mem_comap]; rfl) (l : Ω)
    rw [← key, map_natCast]
    exact hA
  · intro x hx
    rw [ValuationSubring.mem_comap, ← hσ, ← hmK x hx]
    rfl
  · rw [ValuationSubring.mem_comap]
    rfl

theorem UpperTheory.V.Ws.mkTower :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (pr : Bool) (K F : IntermediateField ℚ Ω) [NumberField K] [NumberField F] [IsCMField K] [IsTotallyReal F] [IsAbelianGalois ℚ F],
      Module.finrank ℚ K = 2 → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup) → ∀ g0 : G F Ω,
      ∃ T : Tower D, T.pr = pr ∧ T.K = K ∧ T.F = F ∧ resQ T.F T.g0 = resQ F g0 := by
  intro Ω _ _ _ l _ c D hD pr K F _ _ _ _ _ hK hdec g0
  haveI : NumberField ↥(F ⊔ K) := NumberField.mk
  haveI : IsCMField ↥(F ⊔ K) := mt_cm K F hK
  obtain ⟨h, hhF, hhK⟩ := mt_out K F
  have hP : (D.pl l).valuation (l : Ω) < 1 := hD.pl_over l Fact.out
  let s : Setoid {B : ValuationSubring Ω // B.valuation (l : Ω) < 1 ∧ ∀ x ∈ K, x ∈ B ↔ x ∈ D.pl l} :=
    { r := fun B B' => ∃ g : G F Ω, ∀ x, g x ∈ B.1 ↔ x ∈ B'.1
      iseqv := ⟨fun _ => ⟨1, fun _ => Iff.rfl⟩,
        fun ⟨g, hg⟩ => ⟨g⁻¹, inv_apply_mem_iff_of_apply_mem_iff F _ _ g hg⟩,
        fun ⟨g, hg⟩ ⟨g', hg'⟩ => exists_conj_valuationSubrings_trans F _ _ _ g g' hg hg'⟩ }
  have hex : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ q : Quotient s, ∃ g : G F Ω, ∀ x, g x ∈ A ↔ x ∈ q.out.1 := by
    intro A hA
    obtain ⟨B, hBl, hBK, g, hg⟩ := exists_over_l_place_conj_agreeing_on_field l K F hK h hhF hhK (D.pl l) A hP hA
    obtain ⟨g', hg'⟩ := Quotient.mk_out (s := s) ⟨B, hBl, hBK⟩
    exact ⟨⟦⟨B, hBl, hBK⟩⟧, exists_conj_between_valuationSubrings_of_common F A B _ g g' hg hg'⟩
  have huniq : ∀ (A : ValuationSubring Ω) (q q' : Quotient s) (g g' : G F Ω),
      (∀ x, g x ∈ A ↔ x ∈ q.out.1) → (∀ x, g' x ∈ A ↔ x ∈ q'.out.1) → q = q' := by
    intro A q q' g g' hg hg'
    apply Quotient.out_equiv_out.mp
    exact exists_conj_between_valuationSubrings_of_common F q.out.1 A q'.out.1 g⁻¹ g'⁻¹ (inv_apply_mem_iff_of_apply_mem_iff F A _ g hg) (inv_apply_mem_iff_of_apply_mem_iff F A _ g' hg')
  haveI : Finite (Quotient s) := by
    have hsurj := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥F) Ω
    have hA : ∀ τ : G ℚ Ω, ((D.pl l).comap (τ : Ω →+* Ω)).valuation (l : Ω) < 1 := by
      intro τ
      have key := UpperTheory.V.val_lt_one (σ := τ.toRingEquiv) (A := (D.pl l).comap (τ : Ω →+* Ω)) (A' := D.pl l)
        (fun x => by rw [ValuationSubring.mem_comap]; rfl) (l : Ω)
      rw [← key, map_natCast]
      exact hP
    choose f hf using fun ρ : F ≃ₐ[ℚ] F => hex _ (hA (hsurj ρ).choose)
    refine Finite.of_surjective f (fun q => ?_)
    obtain ⟨τ, hτ⟩ := mt_conj l (D.pl l) q.out.1 hP q.out.2.1
    refine ⟨AlgEquiv.restrictNormalHom F τ, ?_⟩
    obtain ⟨g, hg⟩ := hf (AlgEquiv.restrictNormalHom F τ)
    have hσ := (hsurj (AlgEquiv.restrictNormalHom F τ)).choose_spec
    set σc := (hsurj (AlgEquiv.restrictNormalHom F τ)).choose with hσc
    have hn : τ⁻¹ * σc ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e1 := AlgEquiv.restrictNormal_commutes σc F ⟨x, hx⟩
      have e2 := AlgEquiv.restrictNormal_commutes τ F ⟨x, hx⟩
      have e3 : σc.restrictNormal F = τ.restrictNormal F := hσ
      rw [e3, e2] at e1
      rw [AlgEquiv.mul_apply]
      have e4 : σc x = τ x := e1.symm
      rw [e4, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    let gn : G F Ω := IntermediateField.fixingSubgroupEquiv F ⟨_, hn⟩
    have h1 : ∀ x, gn x ∈ q.out.1 ↔ x ∈ (D.pl l).comap (σc : Ω →+* Ω) := by
      intro x
      rw [ValuationSubring.mem_comap, ← hτ]
      show τ ((τ⁻¹ * σc) x) ∈ D.pl l ↔ _
      rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul]
      rfl
    obtain ⟨k, hk⟩ := exists_conj_valuationSubrings_trans F _ _ _ gn g h1 hg
    have hr : q.out ≈ (f (AlgEquiv.restrictNormalHom F τ)).out := ⟨k, hk⟩
    exact (Quotient.out_equiv_out.mp hr).symm
  refine ⟨⟨pr, K, F, F ⊔ K, hK, rfl, g0, Quotient s, fun q => q.out.1, fun q => q.out.2.1, ?_,
    fun q => q.out.2.2⟩, rfl, rfl, rfl, rfl⟩
  intro A hA
  obtain ⟨q, g, hg⟩ := hex A hA
  exact ⟨q, ⟨g, hg⟩, fun q' ⟨g', hg'⟩ => huniq A q' q g' g hg' hg⟩
