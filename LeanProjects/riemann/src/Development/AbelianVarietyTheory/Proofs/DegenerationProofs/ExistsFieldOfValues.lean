import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem residue_embedding_unique {X : Scheme.{0}} {Ω : CommRingCat.{0}} [Nonempty (Spec Ω)]
    {p q : X} (φ : X.residueField p ⟶ Ω) (ψ : X.residueField q ⟶ Ω)
    (h : Spec.map φ ≫ X.fromSpecResidueField p = Spec.map ψ ≫ X.fromSpecResidueField q) :
    ∃ e : p = q, φ = (X.residueFieldCongr e).hom ≫ ψ := by
  obtain ⟨t⟩ := ‹Nonempty (Spec Ω)›
  have e : p = q := by
    have := congrArg (fun f => f t) h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this
  subst e
  refine ⟨rfl, ?_⟩
  rw [cancel_mono, Spec.map_inj] at h
  simpa using h

theorem essFiniteType_residueField_of_locallyOfFiniteType {X : Scheme.{0}} {R : CommRingCat.{0}}
    (s : X ⟶ Spec R) [LocallyOfFiniteType s] (p : X) (ψ : R ⟶ X.residueField p)
    (h : Spec.map ψ = X.fromSpecResidueField p ≫ s) : ψ.hom.EssFiniteType := by
  haveI : (s p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have e : ψ = CommRingCat.ofHom (algebraMap R (s p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (s p)).inv ≫ s.residueFieldMap p := by
    rw [← Spec.map_inj, h, Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [e]
  refine .comp (RingHom.essFiniteType_algebraMap.mpr inferInstance) (.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.Spec.residueFieldIso R (s p)).inv).2).essFiniteType
    (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap s p)))

theorem exists_fieldOfValues : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  intro X Ω _ x
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  subst hx
  let f : X.residueField p →+* Ω := φ.hom
  refine ⟨f.fieldRange, fun τ τ' => ?_, fun K' _ j => ⟨fun h => ?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
      Spec.map_inj]
    constructor
    · rintro h _ ⟨c, rfl⟩
      exact congrArg (fun g => g.hom c) h
    · intro h
      ext c
      exact h _ ⟨c, rfl⟩
  · let e : K' ≃+* j.fieldRange := j.rangeRestrictFieldEquiv
    let g : X.residueField p →+* K' :=
      e.symm.toRingHom.comp (f.codRestrict j.fieldRange fun c => h ⟨c, rfl⟩)
    refine ⟨Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecResidueField p, ?_⟩
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f c, h ⟨c, rfl⟩⟩)
  · rintro ⟨y, hy⟩
    obtain ⟨⟨q, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K' X).symm.surjective y
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hy
    rw [← Category.assoc, ← Spec.map_comp] at hy
    obtain ⟨e, he⟩ := residue_embedding_unique _ _ hy.symm
    rintro _ ⟨c, rfl⟩
    exact ⟨ψ.hom ((X.residueFieldCongr e).hom.hom c), (congrArg (fun g => g.hom c) he).symm⟩
  · intro K _ _ s hs hxs halg
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ s)
    have hess := essFiniteType_residueField_of_locallyOfFiniteType s p ψ hψ
    rw [Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
    letI : Algebra K (X.residueField p) := ψ.hom.toAlgebra
    let fa : X.residueField p →ₐ[K] Ω :=
      { f with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
    haveI : Algebra.EssFiniteType K (X.residueField p) := hess
    haveI : Algebra.IsAlgebraic K (X.residueField p) :=
      Algebra.IsAlgebraic.of_injective fa f.injective
    haveI : Module.Finite K (X.residueField p) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    refine ⟨fa.fieldRange, ?_, rfl⟩
    exact Module.Finite.equiv (AlgEquiv.ofInjectiveField fa).toLinearEquiv

end GlobalTheory.SS
