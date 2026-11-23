import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

open CategoryTheory AlgebraicGeometry Limits Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.BdDim

theorem TrLe.trdeg_le_of_injective {R A K : Type} [CommRing R] [IsDomain R] [CommRing A] [Field K] [Algebra R A]
    [Algebra R K] [Algebra R (⊥ : Subfield K)] [FaithfulSMul R K]
    (hR : algebraMap R K = (algebraMap (⊥ : Subfield K) K).comp (algebraMap R (⊥ : Subfield K)))
    (f : A →ₐ[R] K) (hf : Function.Injective f) {n : ℕ} (h : TrLe K n) : Algebra.trdeg R A ≤ n := by
  haveI := IsScalarTower.of_algebraMap_eq' hR
  haveI : FaithfulSMul R (⊥ : Subfield K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Function.Injective.of_comp (f := algebraMap (⊥ : Subfield K) K) (by
      have := FaithfulSMul.algebraMap_injective R K
      rwa [IsScalarTower.algebraMap_eq R (⊥ : Subfield K) K] at this))
  let F : Subfield K := { (Subalgebra.algebraicClosure R K).toSubring with
    inv_mem' := fun x hx => IsAlgebraic.inv hx }
  haveI : Algebra.IsAlgebraic R (⊥ : Subfield K) := ⟨fun x => by
    have hx : IsAlgebraic R (x : K) := (bot_le (a := F)) x.2
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R (⊥ : Subfield K) K)
      (algebraMap (⊥ : Subfield K) K).injective).mp hx⟩
  refine (_root_.trdeg_le_of_injective f hf).trans ?_
  rw [← trdeg_add_eq R (⊥ : Subfield K) (A := K), trdeg_eq_zero (R := R) (A := (⊥ : Subfield K)), zero_add]
  exact h

theorem TrLe.ringKrullDim_le {A K : Type} [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K]
    (f : A →+* K) (hf : Function.Injective f) {n : ℕ} (h : TrLe K n) : ringKrullDim A ≤ (n + 1 : ℕ) := by
  obtain ⟨p, hp⟩ := CharP.exists A
  haveI : CharP K p := charP_of_injective_ringHom hf p
  rcases CharP.char_is_prime_or_zero A p with hq | hq
  · haveI := Fact.mk hq
    letI := ZMod.algebra A p
    letI := ZMod.algebra K p
    letI := ZMod.algebra (⊥ : Subfield K) p
    haveI : IsScalarTower ℤ (ZMod p) A := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI : Algebra.FiniteType (ZMod p) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    obtain ⟨s, h1, h2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := A)
    have := h.trdeg_le_of_injective (R := ZMod p) (Subsingleton.elim _ _)
      { f with commutes' := fun r => RingHom.congr_fun (Subsingleton.elim (f.comp (algebraMap _ A)) (algebraMap _ K)) r } hf
    rw [h2] at this
    rw [h1]
    have h3 : s ≤ n := by exact_mod_cast this
    exact_mod_cast h3.trans (Nat.le_succ n)
  · subst hq
    haveI : CharZero A := CharP.charP_to_charZero _
    haveI : CharZero K := CharP.charP_to_charZero _
    have := h.trdeg_le_of_injective (R := ℤ) (Subsingleton.elim _ _) f.toIntAlgHom hf
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one A (RingHom.injective_int _)]
    have h2 : Cardinal.toENat (Algebra.trdeg ℤ A) ≤ n := by
      simpa using Cardinal.toENat.monotone' this
    have h3 : Cardinal.toENat (Algebra.trdeg ℤ A) + 1 ≤ ((n + 1 : ℕ) : ℕ∞) := by
      push_cast
      gcongr
    exact_mod_cast h3

theorem topologicalKrullDim_le_of_trLe_affine {A : Type} [CommRing A] [Algebra.FiniteType ℤ A]
    {S : Set (PrimeSpectrum A)} (hS : IsClosed S) {n : ℕ} (h : ∀ y ∈ S, TrLe y.asIdeal.ResidueField n) :
    topologicalKrullDim S ≤ (n + 1 : ℕ) := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal S).mp hS
  rw [topologicalKrullDim_eq_of_isEmbedding
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).isEmbedding
    (Z := PrimeSpectrum.zeroLocus (I : Set A))
    (by rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]),
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine IntFiniteTypeDim.ringKrullDim_quotient_le_of_minimalPrimes I _ fun P hP => ?_
  haveI := hP.1.1
  haveI : @Algebra.FiniteType ℤ (A ⧸ P) _ _ (Ring.toIntAlgebra _) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mk P).toIntAlgHom Ideal.Quotient.mk_surjective
  exact (h ⟨P, hP.1.1⟩ hP.1.2).ringKrullDim_le (algebraMap (A ⧸ P) P.ResidueField)
    (IsFractionRing.injective _ _)

theorem topologicalKrullDim_le_of_trLe : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℤ) (S : Set X) (n : ℕ), LocallyOfFiniteType p →
    IsClosed S → (∀ y ∈ S, TrLe (X.residueField y) n) → topologicalKrullDim S ≤ (n + 1 : ℕ) := by
  intro X p S n hp hS h
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨R, j, hj, hx, -⟩ := X.exists_affine_mem_range_and_range_subset (x := x.1) (U := ⊤) trivial
  refine ⟨Subtype.val ⁻¹' Set.range j, j.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, hx, ?_⟩
  haveI : Algebra.FiniteType ℤ R := by
    have h1 : LocallyOfFiniteType (j ≫ p) := inferInstance
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ p)
    rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h1
    rw [← RingHom.finiteType_algebraMap]
    rw [Subsingleton.elim (algebraMap ℤ R) φ.hom]
    exact h1
  have e1 := topologicalKrullDim_eq_of_isEmbedding (W := (Subtype.val ⁻¹' Set.range j : Set S)) (Z := Set.range j ∩ S)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])
  have e2 := topologicalKrullDim_eq_of_isEmbedding (W := (j ⁻¹' S : Set (Spec R))) (Z := Set.range j ∩ S)
    (j.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
    (by rw [Set.range_comp, Subtype.range_coe, Set.image_preimage_eq_range_inter])
  rw [← e1, e2]
  refine topologicalKrullDim_le_of_trLe_affine (A := R) (hS.preimage j.continuous) fun (y : Spec R) hy => ?_
  exact (h _ hy).of_ringHom ((Scheme.Spec.residueFieldIso R y).inv ≫ inv (j.residueFieldMap y)).hom

end GlobalTheory.BdDim
