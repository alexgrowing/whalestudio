import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] [Algebra F Ω] [Field F] in

theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  have h1 : IsIntegral A y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hz]
  exact z.2

noncomputable def intToVal (A : ValuationSubring Ω) (M : IntermediateField F Ω) : 𝓞 M →+* A :=
  ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun z =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ M Ω))

noncomputable def cutPrime (A : ValuationSubring Ω) (M : IntermediateField F Ω) : Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal A).comap (intToVal A M)

instance (A : ValuationSubring Ω) (M : IntermediateField F Ω) : (cutPrime A M).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_cutPrime_iff (A : ValuationSubring Ω) (M : IntermediateField F Ω) (z : 𝓞 M) :
    z ∈ cutPrime A M ↔ A.valuation ((z : M) : Ω) < 1 := by
  rw [cutPrime, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem cutPrime_liesOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (M : IntermediateField F Ω) : (cutPrime A M).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, mem_cutPrime_iff, ← hA x]
  rfl

theorem inertia_apply_eq [IsGalois F Ω] {S : Set (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Inertia (F := F) A) {x : Ω} (hx : x ∈ maxUnramifiedOutside F Ω S) :
    σ x = x := by
  classical
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  set E : IntermediateField F Ω := IntermediateField.normalClosure F (IntermediateField.adjoin F ({x} : Set Ω)) Ω with hE
  haveI : FiniteDimensional F E := normalClosure.is_finiteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Normal F E := normalClosure.normal F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_algHom F Ω E.val
  haveI : IsGalois F E := ⟨⟩
  have hxE : x ∈ E := IntermediateField.le_normalClosure (IntermediateField.adjoin F ({x} : Set Ω)) (IntermediateField.mem_adjoin_simple_self F x)
  have hEM : E ≤ maxUnramifiedOutside F Ω S := by
    rw [hE, IntermediateField.normalClosure_le_iff_of_normal]
    exact IntermediateField.adjoin_simple_le_iff.2 hx
  have hEun : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hEM
  haveI hPl : (cutPrime A E).LiesOver v.asIdeal := cutPrime_liesOver hA E
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI : Algebra.FiniteType (𝓞 F) (𝓞 E) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 F) (𝓞 E)
  haveI : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing (G := Gal(E/F)) (A := 𝓞 F) (B := 𝓞 E) (K := F) (L := E)
  have he : (cutPrime A E).ramificationIdx (𝓞 F) = 1 :=
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hEun v hv) hPl
  have hcard : Nat.card ((cutPrime A E).inertia Gal(E/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) v.asIdeal (cutPrime A E),
      Ideal.ramificationIdxIn_eq_ramificationIdx (G := Gal(E/F)) v.asIdeal (cutPrime A E), he]
  set σ' : Gal(E/F) := σ.restrictNormal E with hσ'
  have hmem : σ' ∈ (cutPrime A E).inertia Gal(E/F) := by
    intro z
    show σ' • z - z ∈ cutPrime A E
    rw [mem_cutPrime_iff]
    obtain ⟨-, hσ2⟩ := hσ
    have hy : ((z : E) : Ω) ∈ A :=
      mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ E Ω))
    have hc : (((σ' • z - z : 𝓞 E) : E) : Ω) = σ ((z : E) : Ω) - ((z : E) : Ω) := by
      have h1 := AlgEquiv.restrictNormal_commutes σ E (z : E)
      simp only [IntermediateField.algebraMap_apply] at h1
      rw [← h1, hσ']
      rfl
    rw [hc]
    exact hσ2 _ (A.valuation_le_one ⟨_, hy⟩)
  have hσ'1 : σ' = 1 := by
    haveI hsub : Subsingleton ((cutPrime A E).inertia Gal(E/F)) := (Nat.card_eq_one_iff_unique.1 hcard).1
    have := Subsingleton.elim (⟨σ', hmem⟩ : (cutPrime A E).inertia Gal(E/F)) ⟨1, Subgroup.one_mem _⟩
    exact congrArg Subtype.val this
  have h1 := AlgEquiv.restrictNormal_commutes σ E ⟨x, hxE⟩
  rw [← hσ', hσ'1] at h1
  exact h1.symm

theorem NS_le_fixingSubgroup : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))),
    NS Ω S ≤ (maxUnramifiedOutside F Ω S).fixingSubgroup := by
  intro F Ω _ _ _ _ _ S
  haveI : IsGalois F Ω := ⟨⟩
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : (maxUnramifiedOutside F Ω S).fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois _).2 hM
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := F) A) ⊆
      ((maxUnramifiedOutside F Ω S).fixingSubgroup : Set (G F Ω)) := by
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    show σ ∈ (maxUnramifiedOutside F Ω S).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact inertia_apply_eq hv hA hσA hx
  show (Subgroup.normalClosure _).topologicalClosure ≤ _
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub)
    (InfiniteGalois.fixingSubgroup_isClosed _)

end GlobalTheory.CompanionTheory.GlobalFiniteness
