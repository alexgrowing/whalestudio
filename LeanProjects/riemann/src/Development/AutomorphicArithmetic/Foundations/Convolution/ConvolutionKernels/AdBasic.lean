import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.ReductionMahler
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction Formalism.L2.Host

private theorem finiteAdele_apply_congr {K X : Type} [Field K] [NumberField K] [TopologicalSpace X] [T2Space X]
    {w₁ w₂ : HeightOneSpectrum (𝓞 K)} (h : w₁ = w₂) (f : w₁.adicCompletion K → X) (g : w₂.adicCompletion K → X)
    (hf : Continuous f) (hg : Continuous g)
    (e : ∀ x : K, f (algebraMap K _ x) = g (algebraMap K _ x)) (a : FiniteAdeleRing (𝓞 K) K) :
    f (a w₁) = g (a w₂) := by
  subst h
  exact congrFun ((HeightOneSpectrum.denseRange_algebraMap K w₁).equalizer hf hg (funext e)) _

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

private theorem infiniteAdele_apply_congr {K X : Type} [Field K] [NumberField K] [TopologicalSpace X] [T2Space X]
    {w₁ w₂ : InfinitePlace K} (h : w₁ = w₂) (f : w₁.Completion → X) (g : w₂.Completion → X)
    (hf : Continuous f) (hg : Continuous g)
    (e : ∀ x : K, f (algebraMap K _ x) = g (algebraMap K _ x)) (a : InfiniteAdeleRing K) :
    f (a w₁) = g (a w₂) := by
  subst h
  exact congrFun ((infDense w₁).equalizer hf hg (funext e)) _

private theorem completionEquiv_algebraMap {K : Type} [Field K] [NumberField K] (j : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (CT.compEquiv j.symm v).symm (algebraMap K _ x) = algebraMap K _ (j x) := by
  have h := CT.compEquiv_symm_algebraMap j.symm v (j x)
  rwa [RingEquiv.symm_apply_apply] at h

theorem UpperTheory.ConvolutionTheory.K.adBasic :
    ∀ (K : Type) [Field K] [NumberField K], (∀ (σ : K ≃+* K) (x : K), CT.adMap σ (algebraMap K _ x) = algebraMap K _ (σ x)) ∧
      (∀ a, CT.adMap (RingEquiv.refl K) a = a) ∧ ∀ (σ τ : K ≃+* K) a, CT.adMap (σ.trans τ) a = CT.adMap τ (CT.adMap σ a) := by
  intro K _ _
  refine ⟨fun σ x => ?_, fun a => ?_, fun σ τ a => ?_⟩
  · apply Prod.ext
    · funext u
      exact CT.infEquiv_algebraMap σ u x
    · apply RestrictedProduct.ext
      intro v
      exact completionEquiv_algebraMap σ v x
  · apply Prod.ext
    · funext u
      exact infiniteAdele_apply_congr (w₁ := u.comap (RingEquiv.refl K).toRingHom) (w₂ := u) rfl
        (CT.infEquiv (RingEquiv.refl K) u) id (CT.continuous_infEquiv _ _) continuous_id
        (fun x => CT.infEquiv_algebraMap _ u x) a.1
    · apply RestrictedProduct.ext
      intro v
      exact finiteAdele_apply_congr (w₁ := CT.plMap (RingEquiv.refl K).symm v) (w₂ := v) (by ext x; rfl)
        (CT.compEquiv (RingEquiv.refl K).symm v).symm id (CT.continuous_compEquiv_symm _ _) continuous_id
        (fun x => completionEquiv_algebraMap _ v x) a.2
  · apply Prod.ext
    · funext u
      exact infiniteAdele_apply_congr (w₁ := u.comap (σ.trans τ).toRingHom) (w₂ := (u.comap τ.toRingHom).comap σ.toRingHom) rfl
        (CT.infEquiv (σ.trans τ) u) (fun y => CT.infEquiv τ u (CT.infEquiv σ _ y)) (CT.continuous_infEquiv _ _)
        ((CT.continuous_infEquiv _ _).comp (CT.continuous_infEquiv _ _))
        (fun x => by
          simp only [CT.infEquiv_algebraMap]
          rfl) a.1
    · apply RestrictedProduct.ext
      intro v
      exact finiteAdele_apply_congr (w₁ := CT.plMap (σ.trans τ).symm v) (w₂ := CT.plMap σ.symm (CT.plMap τ.symm v)) (by ext x; rfl)
        (CT.compEquiv (σ.trans τ).symm v).symm
        (fun y => (CT.compEquiv τ.symm v).symm ((CT.compEquiv σ.symm _).symm y))
        (CT.continuous_compEquiv_symm _ _)
        ((CT.continuous_compEquiv_symm _ _).comp (CT.continuous_compEquiv_symm _ _))
        (fun x => by
          simp only [completionEquiv_algebraMap]
          rfl) a.2
