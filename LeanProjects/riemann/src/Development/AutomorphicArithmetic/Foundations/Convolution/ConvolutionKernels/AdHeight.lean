import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.ReductionMahler
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction Formalism.L2.Host

private theorem locHeight_map {A B : Type*} [NormedField A] [NormedField B] {n : ℕ} (e : A →+* B)
    (he : ∀ x, ‖e x‖ = ‖x‖) (g : GL (Fin n) A) :
    AutomorphicForm.locHeight (Matrix.GeneralLinearGroup.map e g) = AutomorphicForm.locHeight g := by
  have hn : ∀ x, ‖e x‖₊ = ‖x‖₊ := fun x => NNReal.eq (he x)
  have h1 : ∀ i j, ((Matrix.GeneralLinearGroup.map e g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j =
      e ((g : Matrix (Fin n) (Fin n) A) i j) := fun _ _ => rfl
  have h2 : ∀ i j, (((Matrix.GeneralLinearGroup.map e g)⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j =
      e (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) := fun i j => by
    rw [← map_inv]
    rfl
  simp only [AutomorphicForm.locHeight, h1, h2, hn]

private theorem infAt_adMap {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K ≃+* K) (u : InfinitePlace K)
    (g : AdelicGLn.AdelicGL K n) :
    infAt u (Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) =
      Matrix.GeneralLinearGroup.map (CT.infEquiv σ u).toRingHom (infAt (u.comap σ.toRingHom) g) := by
  ext i j
  rfl

private theorem finAt_adMap {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K ≃+* K)
    (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    finAt v (Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) =
      Matrix.GeneralLinearGroup.map (CT.compEquiv σ.symm v).symm.toRingHom (finAt (CT.plMap σ.symm v) g) := by
  ext i j
  rfl

private theorem infDense {K : Type} [Field K] (u : InfinitePlace K) :
    DenseRange (algebraMap K u.Completion) := by
  have h1 : DenseRange (fun x : WithAbs u.1 => (x : UniformSpace.Completion (WithAbs u.1))) :=
    UniformSpace.Completion.denseRange_coe
  have h2 : DenseRange (InfinitePlace.Completion.ofCompletion : _ → u.Completion) :=
    (InfinitePlace.Completion.equiv u).symm.surjective.denseRange
  have h3 := h2.comp h1 (InfinitePlace.Completion.continuous_ofCompletion u)
  refine h3.mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x.ofAbs, rfl⟩

private theorem norm_algebraMap_inf {K : Type} [Field K] (u : InfinitePlace K) (x : K) :
    ‖algebraMap K u.Completion x‖ = u x :=
  InfinitePlace.Completion.norm_coe u (WithAbs.toAbs u.1 x)

private theorem norm_infEquiv {K : Type} [Field K] [NumberField K] (σ : K ≃+* K) (u : InfinitePlace K)
    (y : (u.comap σ.toRingHom).Completion) : ‖CT.infEquiv σ u y‖ = ‖y‖ := by
  have h := (infDense (u.comap σ.toRingHom)).equalizer (continuous_norm.comp (CT.continuous_infEquiv σ u))
    continuous_norm (funext fun x => ?_)
  · exact congrFun h y
  simp only [Function.comp_apply]
  rw [CT.infEquiv_algebraMap, norm_algebraMap_inf, norm_algebraMap_inf]
  rfl

private theorem mult_comap_equiv {K : Type} [Field K] [NumberField K] (σ : K ≃+* K) (u : InfinitePlace K) :
    (u.comap σ.toRingHom).mult = u.mult := by
  have h : (u.comap σ.toRingHom).IsReal ↔ u.IsReal := InfinitePlace.isReal_comap_iff σ
  simp only [InfinitePlace.mult]
  by_cases hu : u.IsReal
  · rw [if_pos hu, if_pos (h.2 hu)]
  · rw [if_neg hu, if_neg fun h' => hu (h.1 h')]

private theorem bijective_comap {K : Type} [Field K] [NumberField K] (σ : K ≃+* K) :
    Function.Bijective fun u : InfinitePlace K => u.comap σ.toRingHom := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun u => u.comap σ.symm.toRingHom, fun u => ?_, fun u => ?_⟩
  · ext x
    simp [InfinitePlace.comap_apply]
  · ext x
    simp [InfinitePlace.comap_apply]

private theorem bijective_plMap {K : Type} [Field K] [NumberField K] (σ : K ≃+* K) :
    Function.Bijective (CT.plMap σ.symm) :=
  Function.bijective_iff_has_inverse.2 ⟨CT.plMap σ, CT.plMap_plMap_symm σ, CT.plMap_symm_plMap σ⟩

theorem UpperTheory.ConvolutionTheory.K.adHeight :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n),
      AutomorphicForm.height (Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) = AutomorphicForm.height g := by
  intro K _ _ n σ g
  unfold AutomorphicForm.height
  congr 1
  · rw [← (bijective_comap σ).prod_comp fun w => AutomorphicForm.locHeight (infAt w g) ^ w.mult]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [infAt_adMap, locHeight_map _ (norm_infEquiv σ u), mult_comap_equiv]
  · refine finprod_eq_of_bijective _ (bijective_plMap σ) fun v => ?_
    rw [finAt_adMap, locHeight_map]
    intro y
    have h := CT.norm_compEquiv σ.symm v ((CT.compEquiv σ.symm v).symm y)
    rw [RingEquiv.apply_symm_apply] at h
    exact h.symm
