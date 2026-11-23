import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiRam

theorem prime_dvd_of_mem_different (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (N : ℕ) (hmem : (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L)) {p : ℕ} (hp : p.Prime) (h : p ∣ (discr L).natAbs) :
    p ∣ N ∨ p ∣ (discr K).natAbs := by
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast] at h2
  rw [h1] at h
  exact ((Nat.Prime.dvd_mul hp).1 h).imp (fun h => hp.dvd_of_dvd_pow (h.trans h2)) hp.dvd_of_dvd_pow

theorem sup_adjoin_root (F : IntermediateField ℚ ℂ) [NumberField F] {k : ℕ} (hk : 0 < k) {y : F}
    (hy : y ∈ powIdealElts F k) {z : ℂ} (hz : z ^ k = (y : ℂ)) :
    ∃ _ : NumberField ↥(F ⊔ ℚ⟮z⟯), ∀ p : ℕ, p.Prime → p ∣ (discr ↥(F ⊔ ℚ⟮z⟯)).natAbs →
      p ∣ k ∨ p ∣ (discr F).natAbs := by
  obtain ⟨hy, I, hI⟩ := hy
  have hI' : (I : Submodule (𝓞 F) F) ^ k = Submodule.span (𝓞 F) {y} := by
    rw [← FractionalIdeal.coe_pow, ← hI, FractionalIdeal.coe_spanSingleton]
  set L : IntermediateField ℚ ℂ := F ⊔ ℚ⟮z⟯ with hLdef
  have hzL : z ∈ L := (le_sup_right : ℚ⟮z⟯ ≤ L) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap (x := y))
  have hzQ : IsIntegral ℚ z := isIntegral_trans z hzF
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzQ
  have hLfin : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  letI : NumberField L := NumberField.mk
  letI : Algebra F L := (IntermediateField.inclusion (le_sup_left : F ≤ L)).toRingHom.toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hz' : (⟨z, hzL⟩ : L) ^ k = algebraMap F L y := Subtype.ext hz
  have hzi : IsIntegral F (⟨z, hzL⟩ : L) := Algebra.IsIntegral.isIntegral _
  have htop : F⟮(⟨z, hzL⟩ : L)⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ -
    let M : IntermediateField ℚ ℂ :=
      ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).restrictScalars ℚ
    have hM : L ≤ M := by
      refine sup_le (fun v hv => ?_) (IntermediateField.adjoin_simple_le_iff.mpr ?_)
      · exact ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).algebraMap_mem ⟨v, hv⟩
      · exact ⟨_, IntermediateField.mem_adjoin_simple_self F _, rfl⟩
    obtain ⟨w', hw', hww⟩ := hM hw
    have : w' = ⟨w, hw⟩ := Subtype.ext hww
    rwa [this] at hw'
  have htop' : Algebra.adjoin F {(⟨z, hzL⟩ : L)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzi.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  have hD := GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy _ hI' _ hz' htop'
  exact ⟨inferInstance, fun p hp h => prime_dvd_of_mem_different F L k hD hp h⟩

theorem sup_adjoin_roots {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {h : ℕ} (hh : 0 < h) (S : Set ℂ)
    (hS : S.Finite) (hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts E h, z ^ h = φ y) :
    ∃ _ : NumberField ↥(imField φ ⊔ IntermediateField.adjoin ℚ S), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(imField φ ⊔ IntermediateField.adjoin ℚ S)).natAbs → p ∣ h ∨ p ∣ (discr E).natAbs := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    rw [IntermediateField.adjoin_empty, sup_bot_eq]
    let e₀ : E ≃ₐ[ℚ] imField φ := AlgEquiv.ofInjectiveField φ.toRatAlgHom
    have : FiniteDimensional ℚ (imField φ) := e₀.toLinearEquiv.finiteDimensional
    have hN : NumberField (imField φ) := NumberField.of_module_finite ℚ _
    exact ⟨hN, fun p _ hp => Or.inr (by rwa [discr_eq_discr_of_algEquiv _ e₀])⟩
  | @insert z S _ _ ih =>
    obtain ⟨_, ih⟩ := ih fun w hw => hS' w (Set.mem_insert_of_mem _ hw)
    obtain ⟨y, hy, hz⟩ := hS' z (Set.mem_insert _ _)
    have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ S := (imField_le_iff φ).1 le_sup_left
    obtain ⟨hN, H⟩ := sup_adjoin_root _ hh (map_mem_pow (φ.codRestrict _ hE) hy) hz
    rw [Set.insert_eq, Set.union_comm, IntermediateField.adjoin_union, ← sup_assoc]
    exact ⟨hN, fun p hp hd => (H p hp hd).elim Or.inl (ih p hp)⟩

theorem typeNorm_mem {R : Ranks} (H : Host R) (p q : ℕ) {h : ℕ} {γ : H.E} (hγ : γ ∈ powIdealElts H.E h) :
    typeNorm H p q γ ∈ powIdealElts H.E h := by
  have hσ : ∀ (σ : H.E ≃ₐ[ℚ] H.E) {x}, x ∈ powIdealElts H.E h → σ x ∈ powIdealElts H.E h :=
    fun σ _ hx => map_mem_pow (σ : H.E →+* H.E) hx
  exact prod_mem_pow _ _ fun g _ => mul_mem_pow (npow_mem_pow (hσ _ hγ) _) (npow_mem_pow (hσ _ (hσ _ hγ)) _)

theorem prime_dvd_discr_iSup_kPsi : ∀ (P : Pre) (δ : FieldDat P),
    ∃ _ : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j)).natAbs → p ∣ classNumber P.host.E * (discr P.host.E).natAbs := by
  intro P δ
  let S : Set ℂ := {rootOne (classNumber P.host.E)} ∪ ⋃ j ∈ Set.Icc 1 P.R.m, ⋃ i,
    {z | z ^ δ.basis.h i = P.host.φ₀ (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E))}
  have hS : S.Finite := by
    refine (Set.finite_singleton _).union ((Set.finite_Icc _ _).biUnion fun j _ => Set.finite_iUnion fun i => ?_)
    refine Set.Finite.subset (Polynomial.nthRoots (δ.basis.h i) (P.host.φ₀
      (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E)))).toFinset.finite_toSet fun z hz => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (δ.basis.h_pos i)]
    exact hz
  have hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts P.host.E (classNumber P.host.E), z ^ classNumber P.host.E = P.host.φ₀ y := by
    rintro z (rfl | hz)
    · exact ⟨1, one_mem_pow, by
        rw [map_one]; exact (Complex.isPrimitiveRoot_exp _ (classNumber_ne_zero _)).pow_eq_one⟩
    · simp only [Set.mem_iUnion] at hz
      obtain ⟨j, -, i, hz⟩ := hz
      have hγ : (δ.basis.γ i : P.host.E) ∈ powIdealElts P.host.E (δ.basis.h i) :=
        ⟨(δ.basis.γ i).ne_zero, δ.basis.c i, by
          rw [← coe_toPrincipalIdeal, ← δ.basis.pow_eq i, Units.val_pow_eq_pow_val]; rfl⟩
      obtain ⟨k, hk⟩ : δ.basis.h i ∣ classNumber P.host.E := orderOf_dvd_card
      refine ⟨_, hk ▸ pow_mem_powIdealElts (typeNorm_mem P.host (P.R.sigW j).1 (P.R.sigW j).2 hγ) k, ?_⟩
      rw [hk, pow_mul, map_pow]
      exact congrArg (· ^ k) hz
  obtain ⟨_, H⟩ := sup_adjoin_roots P.host.φ₀ (classNumber_pos P.host.E) S hS hS'
  have hle : (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) ≤ imField P.host.φ₀ ⊔ IntermediateField.adjoin ℚ S := by
    refine iSup₂_le fun j hj => sup_le (sup_le le_sup_left (le_sup_of_le_right ?_)) (le_sup_of_le_right ?_)
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
    · refine IntermediateField.adjoin.mono _ _ _ ?_
      rintro z ⟨i, hz⟩
      exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, Set.mem_iUnion.2 ⟨i, hz⟩⟩)
  have : FiniteDimensional ℚ ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  have hN : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) := NumberField.mk
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  refine ⟨hN, fun p hp hd => (Nat.Prime.dvd_mul hp).2 (H p hp (hd.trans ?_))⟩
  exact Int.natAbs_dvd_natAbs.2 (discr_dvd_discr _ _)

end GlobalTheory.Mem.KPsiRam
