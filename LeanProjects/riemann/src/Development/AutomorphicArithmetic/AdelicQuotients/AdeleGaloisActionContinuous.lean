import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct NumberField.AdeleRing

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_cont {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B] (e : E ⊗[F] A ≃ₐ[E] B)
    (σ : E ≃ₐ[F] E) {ι : Type*} [Fintype ι] (b : ι → E) (c : ι → B → A)
    (hc : ∀ i, Continuous (c i)) (hs : ∀ y, e.symm y = ∑ i, b i ⊗ₜ[F] c i y)
    (hm : Continuous fun a : A => e (1 ⊗ₜ a)) : Continuous (galOf e σ) := by
  have h : ∀ y, galOf e σ y = ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := by
    intro y
    change e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e.symm y)) = _
    rw [hs, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  have h' : (galOf e σ : B → B) = fun y => ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := funext h
  rw [h']
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (hm.comp (hc i))

private theorem galAd_cont (σ : E ≃ₐ[F] E) : Continuous (galAd σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (adeleTensorEquiv F E) σ (Module.finBasis F E) (coord (Module.finBasis F E))
    (continuous_coord _) (adeleTensorEquiv_symm_apply _) ?_
  have h : (fun a : 𝔸[F] => adeleTensorEquiv F E ((1 : E) ⊗ₜ a)) = adeleMap F E := by
    funext a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
  rw [h]
  exact continuous_adeleMap

private theorem galInf_cont (σ : E ≃ₐ[F] E) : Continuous (galInf σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ
    (Module.finBasis F E) (GroundTheory.Global.InfinitePlace.adeleCoord (Module.finBasis F E))
    (GroundTheory.Global.InfinitePlace.continuous_adeleCoord _) (fun y => ?_) ?_
  · rw [AlgEquiv.symm_apply_eq]
    exact (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord _ y).symm
  · have h : (fun a : InfiniteAdeleRing F =>
        GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) ((1 : E) ⊗ₜ a)) =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) := by
      funext a
      rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
    rw [h]
    exact GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap

private theorem galFin_mul (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (y : CompletionsOver E v) :
    galFin σ v (algebraMap (v.adicCompletion F) (CompletionsOver E v) a * y) =
      algebraMap (v.adicCompletion F) (CompletionsOver E v) a * galFin σ v y := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  rw [← tensorEquiv'_tmul_mul]
  change tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 ⊗ₜ a) * t)))) =
    _ * tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v t)))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, ← tensorEquiv'_tmul_mul, map_mul,
    Algebra.TensorProduct.map_tmul]
  simp

private theorem galFin_cont (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (galFin σ v) := by
  let L : CompletionsOver E v →ₗ[v.adicCompletion F] CompletionsOver E v :=
    { toFun := galFin σ v
      map_add' := map_add _
      map_smul' := fun a y => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        exact galFin_mul σ v a y }
  exact IsModuleTopology.continuous_of_linearMap L

private theorem mapGL_cont {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] (n : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (mapGL n f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

end

theorem UpperTheory.adele_galois_action_continuous :
    Compat → RPE → GalCont := by
  intro _ _ F E _ _ _ _ _ σ n
  exact ⟨mapGL_cont n _ (galAd_cont σ), mapGL_cont n _ (galInf_cont σ),
    fun v => mapGL_cont n _ (galFin_cont σ v)⟩
