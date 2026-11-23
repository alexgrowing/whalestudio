import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsRealEmbeddingEqHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AutomorphicArithmetic.Splittings.ExistsCyclicGaloisTensorAlgEquivPi

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

private theorem norm_pi' (T S I : Type) [CommRing T] [CommRing S] [Algebra T S] [Module.Free T S]
    [Module.Finite T S] [Fintype I] [DecidableEq I] (f : I → S) :
    Algebra.norm T f = ∏ i, Algebra.norm T (f i) := by
  have h : Algebra.lmul T (I → S) f =
      LinearMap.pi (fun i => (Algebra.lmul T S (f i)).comp (LinearMap.proj i)) := by
    ext g i
    simp
  rw [Algebra.norm_apply, h, LinearMap.det_pi]
  rfl

private theorem norm_down (F E K L I T : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Fintype I] [DecidableEq I] [Field T] [Algebra K T] [Algebra F T] [IsScalarTower F K T]
    (e : K ⊗[F] E ≃ₐ[K] (I → L)) (x : T) (h : ∃ z : T ⊗[F] E, Algebra.norm T z = x) :
    ∃ y : T ⊗[K] L, Algebra.norm T y = x := by
  obtain ⟨z, rfl⟩ := h
  let e2 : T ⊗[F] E ≃ₐ[T] (I → T ⊗[K] L) :=
    (Algebra.TensorProduct.cancelBaseChange F K T T E).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl e).trans
        (Algebra.TensorProduct.piRight K T T (fun _ : I => L)))
  refine ⟨∏ i, e2 z i, ?_⟩
  rw [map_prod, ← norm_pi', Algebra.norm_eq_of_algEquiv e2 z]

private theorem norm_up (F E K L I : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (e : K ⊗[F] E ≃ₐ[K] (I → L)) (x : K) (h : ∃ y : L, Algebra.norm K y = x) :
    ∃ z : K ⊗[F] E, Algebra.norm K z = x := by
  obtain ⟨y, rfl⟩ := h
  obtain ⟨i0⟩ := ‹Nonempty I›
  refine ⟨e.symm (Pi.mulSingle i0 y), ?_⟩
  rw [← Algebra.norm_eq_of_algEquiv e, AlgEquiv.apply_symm_apply, norm_pi',
    Finset.prod_eq_single i0]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · simp

private theorem transfer (F E A F' T : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [CommRing A] [Algebra F A] [CommRing F'] [Algebra F F'] [CommRing T]
    [Algebra F T] (ψ : F' →ₐ[F] T) (ρ : A →ₐ[F] T) (x : A)
    (h : IsNm F E ((1 : F') ⊗ₜ[F] x)) : ∃ z : T ⊗[F] E, Algebra.norm T z = ρ x := by
  obtain ⟨z, hz⟩ := h
  refine ⟨Algebra.TensorProduct.map (Algebra.TensorProduct.productMap ψ ρ) (AlgHom.id F E) z, ?_⟩
  rw [GlobalTheory.CNorm.tensor_norm_map, hz]
  simp

private theorem local_step (F E K L I A F' T : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Fintype I] [DecidableEq I] [CommRing A] [Algebra F A] [CommRing F'] [Algebra F F'] [Field T]
    [Algebra K T] (e : K ⊗[F] E ≃ₐ[K] (I → L)) (π : A →ₐ[F] K) (ψ : F' →+* T)
    (hψ : ∀ a : F, ψ (algebraMap F F' a) = algebraMap K T (algebraMap F K a)) (x : A)
    (h : IsNm F E ((1 : F') ⊗ₜ[F] x)) : GlobalTheory.CNorm.TNorm K L T (π x) := by
  letI : Algebra F T := ((algebraMap K T).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact norm_down F E K L I T e _ (transfer F E A F' T { ψ with commutes' := hψ }
    ((IsScalarTower.toAlgHom F K T).comp π) x h)

private theorem field_case (F E K A : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] [Field K] [NumberField K] [Algebra F K]
    [CommRing A] [Algebra F A] (π : A →ₐ[F] K) (x : A) (hx : π x ≠ 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), IsNm F E ((1 : v.adicCompletion F) ⊗ₜ[F] x))
    (hi : ∀ v : InfinitePlace F, IsNm F E ((1 : v.Completion) ⊗ₜ[F] x)) :
    ∃ z : K ⊗[F] E, Algebra.norm K z = π x := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, _, _, _, _, I, _, _, _, hC, ⟨e⟩⟩ := UpperTheory.exists_cyclic_galois_tensor_algEquiv_pi F E K
  haveI : NumberField L := NumberField.of_module_finite K L
  refine norm_up F E K L I e _ (GlobalTheory.T.hasseNormPrinciple_of_isCyclic K L inferInstance hC (π x) hx ⟨fun w => ?_, fun a => ?_⟩)
  · obtain ⟨φ, hφ⟩ := GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F K w
    exact local_step F E K L I A _ _ e π φ hφ x (hf _)
  · letI := a
    obtain ⟨v, hv, hσ⟩ := GlobalTheory.CNorm.exists_isReal_embedding_eq_hom
      ((algebraMap K ℝ).comp (algebraMap F K))
    refine local_step F E K L I A v.Completion ℝ e π
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) (fun b => ?_) x (hi v)
    have := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm b)
    rw [hσ] at this
    exact this

end UpperTheory.ConvolutionTheory.D

open UpperTheory.ConvolutionTheory.D in
theorem UpperTheory.ConvolutionTheory.D.hasseEt : UpperTheory.ConvolutionTheory.D.HasseEt := by
  intro F E _ _ _ _ _ _ _ A _ _ _ _ x hf hi
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  have key : ∀ m : MaximalSpectrum A, ∃ y : (A ⧸ m.asIdeal) ⊗[F] E,
      Algebra.norm (A ⧸ m.asIdeal) y = Ideal.Quotient.mk m.asIdeal (x : A) := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : NumberField (A ⧸ m.asIdeal) := NumberField.of_module_finite F _
    exact field_case F E (A ⧸ m.asIdeal) A (Ideal.Quotient.mkₐ F m.asIdeal) x
      (x.isUnit.map (Ideal.Quotient.mkₐ F m.asIdeal)).ne_zero hf hi
  choose y hy using key
  let b := Module.finBasis F E
  let c : Fin (Module.finrank F E) → A := fun j =>
    (IsArtinianRing.equivPi A).symm fun m => (Algebra.TensorProduct.basis _ b).repr (y m) j
  have hc : ∀ m j, Ideal.Quotient.mk m.asIdeal (c j) =
      (Algebra.TensorProduct.basis _ b).repr (y m) j := by
    intro m j
    have := congrFun ((IsArtinianRing.equivPi A).apply_symm_apply
      fun m => (Algebra.TensorProduct.basis _ b).repr (y m) j) m
    exact this
  refine ⟨∑ j, c j ⊗ₜ[F] b j, ?_⟩
  apply (IsArtinianRing.equivPi A).injective
  funext m
  have h1 : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F m.asIdeal) (AlgHom.id F E)
      (∑ j, c j ⊗ₜ[F] b j) = y m := by
    conv_rhs => rw [← (Algebra.TensorProduct.basis _ b).sum_repr (y m)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_apply, ← hc m j,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have h2 := GlobalTheory.CNorm.tensor_norm_map (Ideal.Quotient.mkₐ F m.asIdeal) (∑ j, c j ⊗ₜ[F] b j)
  rw [h1, hy] at h2
  exact h2.symm
