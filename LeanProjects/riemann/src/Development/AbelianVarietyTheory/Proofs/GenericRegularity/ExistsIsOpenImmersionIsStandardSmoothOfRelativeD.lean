import Mathlib

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [Algebra K B] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K B]
    (p : Ideal B) [p.IsPrime] (hp : ∀ q : Ideal B, q.IsPrime → q ≤ p → q = p) :
    Algebra.EssFiniteType K p.ResidueField ∧ Algebra.trdeg K p.ResidueField = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K B
  letI : Algebra (MvPolynomial (Fin d) K) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) B := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.FiniteType K B := .trans (S := MvPolynomial (Fin d) K) inferInstance inferInstance
  refine ⟨.comp K B _, ?_⟩
  obtain ⟨q, hqp, hq, hqo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal (MvPolynomial (Fin d) K))) (q := p.under (MvPolynomial (Fin d) K)) p bot_le
  obtain rfl := hp q hq hqp
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply _ B, Ideal.algebraMap_residueField_eq_zero] at ha
    have : a ∈ q.under (MvPolynomial (Fin d) K) := ha
    rwa [← hqo.over] at this
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) q.ResidueField := by
    let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin d) K)) q
    have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField q.ResidueField :=
      inferInstance
    have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K)
        (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin d) K))
    exact Algebra.IsAlgebraic.trans _ (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField _
  rw [← trdeg_add_eq K (MvPolynomial (Fin d) K), MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero]
  simp

theorem exists_isOpenImmersion_isStandardSmoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) :
    ∃ (B : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ B) (j : Spec B ⟶ X) (_ : IsOpenImmersion j)
      (y : Spec B), j y = x ∧ j ≫ f = Spec.map φ ∧
        φ.hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨A, j, hj, ⟨y, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have h : SmoothOfRelativeDimension (0 + d) (j ≫ f) := inferInstance
  rw [zero_add, ← hφ] at h
  obtain ⟨s, hs, h'⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).1 h
  obtain ⟨t, ht, hty⟩ : ∃ t ∈ s, t ∉ y.asIdeal := by
    by_contra hne
    push Not at hne
    exact y.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hne))
  obtain ⟨z, hz⟩ : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ t]
    exact hty
  refine ⟨.of (Localization.Away t), φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away t)),
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫ j, inferInstance, z,
    ?_, ?_, h' t ht⟩
  · rw [← hz]; rfl
  · rw [Category.assoc, ← hφ, Spec.map_comp]

theorem residueField_fg_trdeg_of_smoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) (hx : ∀ y : X, y ⤳ x → y = x) :
    letI : Algebra K (X.residueField x) :=
      (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    (⊤ : IntermediateField K (X.residueField x)).FG ∧ Algebra.trdeg K (X.residueField x) = d := by
  obtain ⟨B, φ, j, hj, y, rfl, hjf, hφ⟩ :=
    exists_isOpenImmersion_isStandardSmoothOfRelativeDimension f d hf x
  letI : Algebra K (X.residueField (j y)) :=
    (Spec.preimage (X.fromSpecResidueField (j y) ≫ f)).hom.toAlgebra
  letI : Algebra K B := φ.hom.toAlgebra
  haveI : y.asIdeal.IsPrime := y.isPrime
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d K B := hφ
  obtain ⟨h1, h2⟩ := residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension (K := K) d
    y.asIdeal (fun q hq hqy => by
      have hs : (⟨q, hq⟩ : PrimeSpectrum B) ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).mp hqy
      have := j.isOpenEmbedding.injective (hx _ (hs.map j.continuous))
      exact congrArg PrimeSpectrum.asIdeal this)
  let e : X.residueField (j y) ≅ CommRingCat.of y.asIdeal.ResidueField :=
    asIso (j.residueFieldMap y) ≪≫ Scheme.Spec.residueFieldIso B y
  have he : Spec.preimage (X.fromSpecResidueField (j y) ≫ f) ≫ e.hom =
      φ ≫ CommRingCat.ofHom (algebraMap B y.asIdeal.ResidueField) := by
    rw [← Spec.map_inj, ← cancel_epi (Spec.map (Scheme.Spec.residueFieldIso B y).inv)]
    simp only [e, Iso.trans_hom, asIso_hom, Spec.map_comp, Spec.map_preimage, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hjf]
    rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  let e' : X.residueField (j y) ≃ₐ[K] y.asIdeal.ResidueField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congr($(he).hom a) }
  refine ⟨IntermediateField.fg_top_iff.mpr ?_, ?_⟩
  · exact Algebra.EssFiniteType.of_surjective e'.symm.toAlgHom e'.symm.surjective
  · rw [e'.trdeg_eq, h2]

theorem residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ), SmoothOfRelativeDimension d f → ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X), letI : Algebra K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) := (Spec.preimage (X.fromSpecResidueField (hZ.1 : IsIrreducible Z).genericPoint ≫ f)).hom.toAlgebra; (⊤ : IntermediateField K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint)).FG ∧ Algebra.trdeg K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) = d := by
  intro K _ X f d hf Z hZ
  refine residueField_fg_trdeg_of_smoothOfRelativeDimension f d hf _ fun y hy => ?_
  have hg := (hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have h1 : Z ⊆ closure {y} := by
    rw [← hg.def]
    exact specializes_iff_closure_subset.mp hy
  have h2 : closure {y} ⊆ Z := hZ.2 isIrreducible_singleton.closure h1
  exact (hy.antisymm (hg.specializes (h2 (subset_closure rfl)))).eq

end GlobalTheory
