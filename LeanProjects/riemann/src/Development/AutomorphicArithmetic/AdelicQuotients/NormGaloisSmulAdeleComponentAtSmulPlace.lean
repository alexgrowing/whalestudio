import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem continuous_infMap {M M' : Type} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : InfinitePlace M') :
    Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  exact NumberField.LiesOver.continuous_completionMap

private theorem norm_algebraMap_of_smul_eq (σ : E ≃ₐ[F] E) (u w : HeightOneSpectrum (𝓞 E))
    (h : σ • u = w) (l : E) :
    ‖algebraMap E (w.adicCompletion E) (σ l)‖ = ‖algebraMap E (u.adicCompletion E) l‖ := by
  subst h
  exact norm_algebraMap_smul σ u l

private theorem norm_finMap (σ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E))
    (y : (comapPrime (σ : E ≃+* E) w).adicCompletion E) :
    ‖finiteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖ := by
  refine (HeightOneSpectrum.denseRange_algebraMap E (comapPrime (σ : E ≃+* E) w)).induction_on
    (p := fun y => ‖finiteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖) y
    (isClosed_eq (continuous_norm.comp (continuous_finiteCompletionMap _ w)) continuous_norm)
    fun l => ?_
  rw [finiteCompletionMap_algebraMap]
  exact norm_algebraMap_of_smul_eq σ _ w (by rw [comapPrime_eq_inv_smul, smul_inv_smul]) l

private theorem norm_algebraMap_completion (w : InfinitePlace E) (x : E) :
    ‖algebraMap E w.Completion x‖ = w x :=
  InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ x)

private theorem norm_infMap (σ : E ≃ₐ[F] E) (w : InfinitePlace E)
    (y : (w.comap ((σ : E ≃+* E) : E →+* E)).Completion) :
    ‖infiniteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖ := by
  refine InfinitePlace.Completion.induction_on _ y
    (isClosed_eq (continuous_norm.comp (continuous_infMap _ w)) continuous_norm) fun a => ?_
  change ‖infiniteCompletionMap (σ : E ≃+* E) w (algebraMap E _ a.ofAbs)‖ =
    ‖algebraMap E (w.comap ((σ : E ≃+* E) : E →+* E)).Completion a.ofAbs‖
  rw [infiniteCompletionMap_algebraMap, norm_algebraMap_completion, norm_algebraMap_completion,
    InfinitePlace.comap_apply]
  rfl

private theorem norm_snd_congr (a : 𝔸[E]) {w₁ w₂ : HeightOneSpectrum (𝓞 E)} (h : w₁ = w₂) :
    ‖a.2 w₁‖ = ‖a.2 w₂‖ := by
  subst h
  rfl

private theorem norm_fst_congr (a : 𝔸[E]) {w₁ w₂ : InfinitePlace E} (h : w₁ = w₂) :
    ‖a.1 w₁‖ = ‖a.1 w₂‖ := by
  subst h
  rfl

end

theorem UpperTheory.norm_galois_smul_adele_component_at_smul_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (a : 𝔸[E]),
        (∀ w : HeightOneSpectrum (𝓞 E), ‖(galAd σ a).2 (σ • w)‖ = ‖a.2 w‖) ∧
        ∀ w : InfinitePlace E, ‖(galAd σ a).1 (σ • w)‖ = ‖a.1 w‖ := by
  intro F E _ _ _ _ _ σ a
  rw [galAd_apply]
  constructor
  · intro w
    rw [smul_snd, norm_finMap]
    exact norm_snd_congr a (by rw [comapPrime_eq_inv_smul, inv_smul_smul])
  · intro w
    rw [smul_fst, norm_infMap]
    exact norm_fst_congr a (by rw [comap_eq_inv_smul, inv_smul_smul])
