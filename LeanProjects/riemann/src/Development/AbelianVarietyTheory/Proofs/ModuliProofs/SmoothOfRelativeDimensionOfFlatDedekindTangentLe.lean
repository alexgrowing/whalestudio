import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SmoothDedekind

open GlobalTheory.SmoothTangent IsLocalRing

def pointOfDerivations {k B C : Type} [CommRing k] [CommRing B] [Field C] [Algebra k B]
    [Algebra k C] [Algebra B C] [IsScalarTower k B C] {r : ℕ} (D : Fin r → Derivation k B C) :
    B →+* TrivSqZeroExt C (Fin r → C) where
  toFun b := (algebraMap B C b, fun i ↦ D i b)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap B C)) (funext fun i ↦ (D i).map_one_eq_zero)
  map_mul' a b := TrivSqZeroExt.ext (map_mul (algebraMap B C) a b) (funext fun i ↦ by
    change D i (a * b) = algebraMap B C a * D i b + D i a * algebraMap B C b
    rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def, mul_comm (D i a)])
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap B C)) (funext fun i ↦ map_zero (D i))
  map_add' a b := TrivSqZeroExt.ext (map_add (algebraMap B C) a b)
    (funext fun i ↦ map_add (D i) a b)

theorem exists_point_of_isMaximal (k : Type) [Field k] [PerfectField k] {B : Type} [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] (x : Ideal B) [x.IsMaximal] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (r : ℕ)
      (g : B →+* TrivSqZeroExt C (Fin r → C)), Module.finrank (B ⧸ x) x.Cotangent ≤ r ∧
      (∀ c : k, (g (algebraMap k B c)).snd = 0) ∧
      ∀ lam : (Fin r → C) →ₗ[C] C, (∀ b, lam (g b).snd = 0) → lam = 0 := by
  let := Ideal.Quotient.field x
  let C := AlgebraicClosure (B ⧸ x)
  have : Module.Finite C (Derivation k B C) := .equiv (derivationEquivDual k B C).symm
  let D := Module.finBasis C (Derivation k B C)
  refine ⟨C, inferInstance, inferInstance, _, pointOfDerivations D,
    finrank_cotangent_le_finrank_derivation k x C, fun c ↦ funext fun i ↦ (D i).map_algebraMap c,
    fun lam h ↦ ?_⟩
  have h₀ : ∑ i, lam (Pi.single i 1) • D i = 0 := by
    ext b
    have h₁ : lam (fun i ↦ D i b) = 0 := h b
    rw [LinearMap.pi_apply_eq_sum_univ] at h₁
    have h₂ : (∑ i, lam (Pi.single i 1) • D i) b = ∑ i, lam (Pi.single i 1) * D i b := by
      have := map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := B) (M := C))
        (fun i ↦ lam (Pi.single i 1) • D i) Finset.univ
      have := congrFun this b
      rw [Finset.sum_apply] at this
      exact this
    rw [h₂, Derivation.zero_apply, ← h₁]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_
  simpa using Fintype.linearIndependent_iff.mp D.linearIndependent _ h₀ i

theorem exists_isStandardSmoothOfRelativeDimension_of_isLocalization (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] (q : Ideal A)
    [q.IsPrime] (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L q] [Algebra R L]
    [IsScalarTower R A L] [Algebra.FormallySmooth R L] {d : ℕ}
    (hd : Module.finrank L Ω[L⁄R] = d) :
    ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away f) := by
  let e : L ≃ₐ[A] Localization.AtPrime q := IsLocalization.algEquiv q.primeCompl _ _
  have : Algebra.IsSmoothAt R q := Algebra.FormallySmooth.of_equiv (e.restrictScalars R)
  refine exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt R q ?_
  let : Algebra L (Localization.AtPrime q) := e.toRingHom.toAlgebra
  have : IsScalarTower R L (Localization.AtPrime q) :=
    .of_algebraMap_eq fun r ↦ ((e.restrictScalars R).commutes r).symm
  have : Algebra.FormallyEtale L (Localization.AtPrime q) :=
    .of_equiv (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (R := L) fun _ ↦ rfl)
  have : Algebra.EssFiniteType A L := .of_isLocalization L q.primeCompl
  have : Algebra.EssFiniteType R L := .comp R A L
  have := IsLocalization.AtPrime.isLocalRing L q
  have : Module.Free L Ω[L⁄R] := Module.free_of_flat_of_isLocalRing
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R L
    (Localization.AtPrime q)).finrank_eq, Module.finrank_baseChange, hd]

theorem finrank_kaehler_eq_of_formallyUnramified (R V L : Type*) [CommRing R] [CommRing V]
    [CommRing L] [Algebra R V] [Algebra V L] [Algebra R L] [IsScalarTower R V L]
    [Algebra.FormallyUnramified R V] :
    Module.finrank L Ω[L⁄R] = Module.finrank L Ω[L⁄V] := by
  refine (LinearEquiv.ofBijective (KaehlerDifferential.map R V L L)
    ⟨?_, KaehlerDifferential.map_surjective R V L⟩).finrank_eq
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R V L x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

theorem le_ringKrullDim_quotient_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {d : WithBot ℕ∞} (hd : ∀ q ∈ minimalPrimes S, d ≤ ringKrullDim (S ⧸ q)) :
    ∀ p ∈ minimalPrimes R, d ≤ ringKrullDim (R ⧸ p) := by
  intro p hp
  have := hp.1.1
  have h : p.map (e : R →+* S) ∈ minimalPrimes S := by
    refine ⟨⟨Ideal.map_isPrime_of_equiv e, bot_le⟩, fun q hq hle ↦ ?_⟩
    have := hq.1
    rw [Ideal.map_le_iff_le_comap]
    refine hp.2 ⟨Ideal.comap_isPrime _ q, bot_le⟩ ?_
    refine (Ideal.comap_mono hle).trans ?_
    rw [Ideal.comap_map_of_bijective (e : R →+* S) e.bijective]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv p _ e rfl)]
  exact hd _ h

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem exists_isStandardSmoothOfRelativeDimension_of_localization (o V K : Type) [CommRing o]
    [IsNoetherianRing o] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [PerfectField (ResidueField V)] [Field K] [Algebra o V] [Algebra V K] [Algebra o K]
    [IsScalarTower o V K] [IsFractionRing V K] (M : Submonoid o) [IsLocalization M V]
    {A : Type} [CommRing A] [Algebra o A] [Algebra.FiniteType o A] [Module.Flat o A] {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[o] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[o] A) ⧸ p))
    (x : Ideal (ResidueField V ⊗[o] A)) [x.IsMaximal]
    (hx : Module.finrank ((ResidueField V ⊗[o] A) ⧸ x) x.Cotangent ≤ d) :
    ∃ f ∉ x.comap (Algebra.TensorProduct.includeRight : A →ₐ[o] ResidueField V ⊗[o] A).toRingHom,
      Algebra.IsStandardSmoothOfRelativeDimension d o (Localization.Away f) := by
  let ρ : V →ₐ[o] ResidueField V := IsScalarTower.toAlgHom o V _
  have hρ : Function.Surjective ρ := residue_surjective
  let φ : V ⊗[o] A →+* ResidueField V ⊗[o] A :=
    (Algebra.TensorProduct.map ρ (AlgHom.id o A)).toRingHom
  have hφ : Function.Surjective φ :=
    LinearMap.rTensor_surjective A (g := ρ.toLinearMap) hρ
  have hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V (V ⊗[o] A)) := by
    have h := Algebra.TensorProduct.rTensor_ker (R := o) (C := A) ρ hρ
    rw [show RingHom.ker ρ = maximalIdeal V from ker_residue] at h
    exact h
  have hd' := le_ringKrullDim_quotient_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange o V K K A).toRingEquiv hd
  obtain ⟨h₁, -, h₂, h₃, -⟩ :=
    isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K hd' φ hφ hker x hx
  have : Algebra.FinitePresentation V (V ⊗[o] A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨-, -, h₄⟩ :=
    isSmoothAt_of_flat_of_isRegularLocalRing V φ hφ hker x (Localization.AtPrime x)
  rw [h₃] at h₄
  let L := Localization.AtPrime (x.comap φ)
  have h₅ : Module.finrank L Ω[L⁄V] = d := by exact_mod_cast h₄
  have : Algebra.FinitePresentation o A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.FormallyEtale o V := .of_isLocalization M
  have : Algebra.FormallySmooth o L := .comp o V L
  have := IsLocalization.tensorRight (S := A) V M
  have hL := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A M) L (x.comap φ)
  have hq : (x.comap φ).comap (algebraMap A (V ⊗[o] A)) = x.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[o] ResidueField V ⊗[o] A).toRingHom := by
    rw [Ideal.comap_comap]
    congr 1
  rw [← hq]
  exact exists_isStandardSmoothOfRelativeDimension_of_isLocalization o _ L
    ((finrank_kaehler_eq_of_formallyUnramified o V L).trans h₅)

theorem exists_isStandardSmoothOfRelativeDimension_of_isMaximal (o : Type) [CommRing o]
    [IsDedekindDomain o] [CharZero o] [Algebra.FiniteType ℤ o]
    {A : Type} [CommRing A] [Algebra o A] [Algebra.FiniteType o A] [Module.Flat o A] {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (FractionRing o ⊗[o] A),
      (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] A) ⧸ p))
    (ht : ∀ (C : Type) [Field C] [IsAlgClosed C] (r : ℕ) (g : A →+* TrivSqZeroExt C (Fin r → C)),
      (∀ c : o, (g (algebraMap o A c)).snd = 0) →
      (∀ lam : (Fin r → C) →ₗ[C] C, (∀ a, lam (g a).snd = 0) → lam = 0) → r ≤ d)
    (q : Ideal A) [q.IsMaximal] :
    ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d o (Localization.Away f) := by
  let m := q.under o
  have : Algebra.FiniteType ℤ A := .trans (S := o) ‹_› ‹_›
  have : Finite (A ⧸ q) := by
    let := Ideal.Quotient.field q
    have h : ((Ideal.Quotient.mk q).comp (algebraMap ℤ A)).FiniteType :=
      (RingHom.finiteType_algebraMap.mpr ‹_›).comp_surjective Ideal.Quotient.mk_surjective
    refine @finite_field_of_finiteType_int _ _ (RingHom.finiteType_algebraMap.mp ?_)
    exact (congrArg RingHom.FiniteType (RingHom.ext_int _ _)).mp h
  let e : m.ResidueField →ₐ[o] q.ResidueField := Ideal.ResidueField.mapₐ m q (Algebra.ofId o A) rfl
  have : Finite m.ResidueField := .of_injective e e.toRingHom.injective
  have hm : m ≠ ⊥ := fun h ↦ by
    have : Finite o := .of_injective (algebraMap o m.ResidueField)
      ((RingHom.injective_iff_ker_eq_bot _).mpr (m.ker_algebraMap_residueField.trans h))
    exact not_finite o
  have : m.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hm
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hm
    (Localization.AtPrime m)
  let χ : m.ResidueField ⊗[o] A →ₐ[o] q.ResidueField :=
    Algebra.TensorProduct.lift e (IsScalarTower.toAlgHom o A _) fun _ _ ↦ .all _ _
  let ψ : A →+* m.ResidueField ⊗[o] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[o] m.ResidueField ⊗[o] A).toRingHom
  have hψ : Function.Surjective ψ :=
    TensorProduct.mk_surjective o A _ m.algebraMap_residueField_surjective
  have hχψ (a : A) : χ (ψ a) = algebraMap A _ a := by simp [χ, ψ]
  have hχ : Function.Surjective χ.toRingHom := fun y ↦ by
    obtain ⟨a, rfl⟩ := q.algebraMap_residueField_surjective y
    exact ⟨_, hχψ a⟩
  let x := RingHom.ker χ.toRingHom
  have : x.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ
  have hq : x.comap ψ = q := by
    ext a
    rw [← Ideal.algebraMap_residueField_eq_zero (I := q), ← hχψ]
    rfl
  obtain ⟨C, _, _, r, g, h₁, h₂, h₃⟩ := exists_point_of_isMaximal m.ResidueField x
  have hr : r ≤ d := by
    refine ht C r (g.comp ψ) (fun c ↦ ?_) fun lam h ↦ h₃ lam fun b ↦ ?_
    · have := h₂ (algebraMap o _ c)
      rw [← IsScalarTower.algebraMap_apply,
        ← (Algebra.TensorProduct.includeRight : A →ₐ[o] m.ResidueField ⊗[o] A).commutes] at this
      exact this
    · obtain ⟨a, rfl⟩ := hψ b
      exact h a
  rw [← hq]
  exact exists_isStandardSmoothOfRelativeDimension_of_localization o (Localization.AtPrime m)
    (FractionRing o) m.primeCompl hd x (h₁.trans hr)

theorem smoothOfRelativeDimension_of_flat_of_tangent_le : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), Algebra.FiniteType ℤ o → Flat s → LocallyOfFiniteType s → (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : o →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X), x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) → (∀ lam : (Fin r → K) →ₗ[K] K, spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) → SmoothOfRelativeDimension d s := by
  intro o _ _ _ X s d _ _ _ hd ht
  have key (z : X) : ∃ U : X.Opens, z ∈ U ∧ SmoothOfRelativeDimension d (U.ι ≫ s) := by
    obtain ⟨A, _, _, j, _, p, hp, hj⟩ := exists_affine_chart_over s z
    have : Algebra.FiniteType o A := RingHom.finiteType_algebraMap.mp <|
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
        (φ := CommRingCat.ofHom (algebraMap o A))).mp (hj ▸ inferInstance)
    have : Module.Flat o A := RingHom.flat_algebraMap_iff.mp <|
      (HasRingHomProperty.Spec_iff (P := @Flat)
        (φ := CommRingCat.ofHom (algebraMap o A))).mp (hj ▸ inferInstance)
    obtain ⟨q, hq, hpq⟩ := Ideal.exists_le_maximal _ p.isPrime.ne_top
    obtain ⟨f, hf, hs⟩ := exists_isStandardSmoothOfRelativeDimension_of_isMaximal o
      (hd A j ‹_› hj) (d := d) (fun C _ _ r g h₁ h₂ ↦ by
        refine ht C r ((TrivSqZeroExt.fstHom C C (Fin r → C)).toRingHom.comp
          (g.comp (algebraMap o A))) (spMap g ≫ j) ?_ fun lam h ↦ h₂ lam fun a ↦ ?_
        · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          refine RingHom.ext fun c ↦ TrivSqZeroExt.ext ?_ ?_
          · rfl
          · exact h₁ c
        · simp only [constPt, ← Category.assoc, cancel_mono, ← Spec.map_comp,
            ← CommRingCat.ofHom_comp] at h
          have h' := congrArg (fun t ↦ TrivSqZeroExt.snd (t.hom a)) (Spec.map_injective h)
          simpa [dirMap, TrivSqZeroExt.algebraMap_eq_inl] using h') q
    let j' := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ j
    have hs' : SmoothOfRelativeDimension d (j' ≫ s) := by
      rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq,
        HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
      exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hs)
    refine ⟨j'.opensRange, ?_, ?_⟩
    · obtain ⟨t, ht⟩ :
          p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
        rw [PrimeSpectrum.localization_away_comap_range _ f]
        exact fun h ↦ hf (hpq h)
      refine ⟨t, ?_⟩
      rw [← hp, ← ht]
      rfl
    · rw [← j'.isoOpensRange_inv_comp, Category.assoc]
      have := smoothOfRelativeDimension_comp 0 d j'.isoOpensRange.inv (j' ≫ s)
      rwa [zero_add] at this
  choose U hU hs using key
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  exact IsZariskiLocalAtSource.of_iSup_eq_top U
    (top_le_iff.mp fun z _ ↦ le_iSup U z (hU z)) hs

end GlobalTheory.SmoothDedekind
