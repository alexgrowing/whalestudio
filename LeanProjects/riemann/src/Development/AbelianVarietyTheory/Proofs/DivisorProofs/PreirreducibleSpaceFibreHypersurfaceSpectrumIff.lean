import Mathlib
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.FibreHyp

section defs
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]

abbrev Ik : Ideal (MvPolynomial σ k) := Ideal.span {MvPolynomial.map (algebraMap A k) f}

abbrev Lk := Localization.Away (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))

abbrev LA := Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)

def rhoK : MvPolynomial σ k →ₐ[k] Lk f g k :=
  (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mkₐ k (Ik f k))

def rhoA : MvPolynomial σ A →ₐ[A] LA f g :=
  (IsScalarTower.toAlgHom A (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g)).comp
    (Ideal.Quotient.mkₐ A (Ideal.span {f}))

lemma rhoK_apply (p : MvPolynomial σ k) :
    rhoK f g k p = algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k) (Ideal.Quotient.mk (Ik f k) p) := rfl

lemma rhoA_apply (p : MvPolynomial σ A) :
    rhoA f g p = algebraMap (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g) (Ideal.Quotient.mk _ p) := rfl

def fwd0 : MvPolynomial σ A →ₐ[A] Lk f g k :=
  MvPolynomial.aeval (fun i => rhoK f g k (MvPolynomial.X i))

lemma fibreHypersurfaceForwardPolynomial_apply (p : MvPolynomial σ A) :
    fwd0 f g k p = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [fwd0, ← MvPolynomial.aeval_map_algebraMap k]
  conv_rhs => rw [MvPolynomial.aeval_unique (rhoK f g k)]
  rfl

def fwd1 : (MvPolynomial σ A ⧸ Ideal.span {f}) →ₐ[A] Lk f g k :=
  Ideal.Quotient.liftₐ (Ideal.span {f}) (fwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceForwardPolynomial_apply f g k f]
    have : rhoK f g k (MvPolynomial.map (algebraMap A k) f) = 0 := by
      simp [rhoK, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, mul_zero])

lemma fibreHypersurfaceForwardQuotient_mk (p : MvPolynomial σ A) :
    fwd1 f g k (Ideal.Quotient.mk _ p) = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [← fibreHypersurfaceForwardPolynomial_apply]; rfl

def fwd2 : LA f g →ₐ[A] Lk f g k :=
  IsLocalization.Away.liftAlgHom (S := LA f g) (Ideal.Quotient.mk (Ideal.span {f}) g) (f := fwd1 f g k) (by
    rw [fibreHypersurfaceForwardQuotient_mk, rhoK_apply]
    exact IsLocalization.Away.algebraMap_isUnit (S := Lk f g k)
      (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)))

def fwd : k ⊗[A] LA f g →ₐ[k] Lk f g k :=
  Algebra.TensorProduct.lift (Algebra.ofId k _) (fwd2 f g k) (fun _ _ => Commute.all _ _)

def bwd0 : MvPolynomial σ k →ₐ[k] k ⊗[A] LA f g :=
  MvPolynomial.aeval (fun i => Algebra.TensorProduct.includeRight (rhoA f g (MvPolynomial.X i)))

lemma fibreHypersurfaceBackwardPolynomial_map (p : MvPolynomial σ A) :
    bwd0 f g k (MvPolynomial.map (algebraMap A k) p) =
      Algebra.TensorProduct.includeRight (R := A) (A := k) (rhoA f g p) := by
  rw [bwd0, MvPolynomial.aeval_map_algebraMap]
  change _ = ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g)) p
  conv_rhs => rw [MvPolynomial.aeval_unique ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g))]
  rfl

def bwd1 : (MvPolynomial σ k ⧸ Ik f k) →ₐ[k] k ⊗[A] LA f g :=
  Ideal.Quotient.liftₐ _ (bwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceBackwardPolynomial_map]
    have : rhoA f g f = 0 := by
      simp [rhoA, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, map_zero, mul_zero])

lemma fibreHypersurfaceBackwardQuotient_mk (p : MvPolynomial σ k) : bwd1 f g k (Ideal.Quotient.mk _ p) = bwd0 f g k p := rfl

def bwd2 : Lk f g k →ₐ[k] k ⊗[A] LA f g :=
  IsLocalization.Away.liftAlgHom (S := Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)) (f := bwd1 f g k) (by
    rw [fibreHypersurfaceBackwardQuotient_mk, fibreHypersurfaceBackwardPolynomial_map, rhoA_apply]
    exact (IsLocalization.Away.algebraMap_isUnit (S := LA f g)
      (Ideal.Quotient.mk (Ideal.span {f}) g)).map (Algebra.TensorProduct.includeRight (R := A) (A := k)))

lemma fwd_bwd : (fwd f g k).comp (bwd2 f g k) = AlgHom.id k _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have h1 := fibreHypersurfaceForwardQuotient_mk f g k (MvPolynomial.X i)
  have h2 := fibreHypersurfaceBackwardPolynomial_map f g k (MvPolynomial.X i)
  simp only [MvPolynomial.map_X, rhoK_apply, rhoA_apply] at h1 h2
  change fwd f g k (bwd2 f g k (algebraMap _ (Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.X i)))) =
    algebraMap _ (Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.X i))
  simp only [bwd2, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    fibreHypersurfaceBackwardQuotient_mk, h2, Algebra.TensorProduct.includeRight_apply, fwd, Algebra.TensorProduct.lift_tmul, map_one,
    _root_.one_mul, fwd2, h1]

lemma bwd_fwd : (bwd2 f g k).comp (fwd f g k) = AlgHom.id k _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {f}) g))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    have h1 := fibreHypersurfaceForwardQuotient_mk f g k (MvPolynomial.X i)
    have h2 := fibreHypersurfaceBackwardPolynomial_map f g k (MvPolynomial.X i)
    simp only [MvPolynomial.map_X, rhoK_apply, rhoA_apply] at h1 h2
    change bwd2 f g k (fwd f g k ((1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i)))) =
      (1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i))
    simp only [fwd, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul, fwd2, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, bwd2, fibreHypersurfaceBackwardQuotient_mk, h2,
      Algebra.TensorProduct.includeRight_apply]

lemma rhoK_comp : (rhoK f g k).toRingHom =
    (algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mk (Ik f k)) := rfl

theorem isEmbedding_comap_rhoK : Topology.IsEmbedding (PrimeSpectrum.comap (rhoK f g k).toRingHom) := by
  rw [rhoK_comp, PrimeSpectrum.comap_comp]
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding.comp
    (PrimeSpectrum.localization_away_isOpenEmbedding (Lk f g k)
      (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))).isEmbedding

theorem range_comap_rhoK : Set.range (PrimeSpectrum.comap (rhoK f g k).toRingHom) =
    PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
      PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      have : (rhoK f g k).toRingHom (MvPolynomial.map (algebraMap A k) f) = 0 := by
        simp [rhoK_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
      rw [this]; exact q.asIdeal.zero_mem
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      intro h
      have hu : IsUnit ((rhoK f g k).toRingHom (MvPolynomial.map (algebraMap A k) g)) :=
        IsLocalization.Away.algebraMap_isUnit (S := Lk f g k)
          (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  · rintro ⟨hf, hg⟩
    have h1 : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ik f k))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.zeroLocus_span]
      exact hf
    obtain ⟨q0, rfl⟩ := h1
    have h2 : q0 ∈ Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Lk f g k)
        (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))]
      intro h
      apply hg
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      exact h
    obtain ⟨q, rfl⟩ := h2
    exact ⟨q, by rw [rhoK_comp, PrimeSpectrum.comap_comp_apply]⟩

end defs

theorem preirreducibleSpace_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    PreirreducibleSpace X ↔ PreirreducibleSpace Y := by
  have key : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y),
      PreirreducibleSpace X → PreirreducibleSpace Y := by
    intro X Y _ _ e h
    refine ⟨?_⟩
    have := (PreirreducibleSpace.isPreirreducible_univ (X := X)).image e e.continuous.continuousOn
    rwa [Set.image_univ_of_surjective e.surjective] at this
  exact ⟨key e, key e.symm⟩

theorem spectrum_fibre_preirreducible_iff (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A)
    (k : Type) [Field k] [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔
      IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
        PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by
  let e : (k ⊗[A] LA f g) ≃ₐ[k] Lk f g k :=
    AlgEquiv.ofAlgHom (fwd f g k) (bwd2 f g k) (fwd_bwd f g k) (bwd_fwd f g k)
  rw [preirreducibleSpace_congr (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv), ← range_comap_rhoK,
    isPreirreducible_iff_preirreducibleSpace]
  exact preirreducibleSpace_congr (isEmbedding_comap_rhoK f g k).toHomeomorph

end GlobalTheory.FibreHyp
