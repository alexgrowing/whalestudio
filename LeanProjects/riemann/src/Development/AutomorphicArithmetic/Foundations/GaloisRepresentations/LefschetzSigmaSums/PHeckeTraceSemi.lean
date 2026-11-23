import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.LKDef

section Transport

variable {Γ H V V' : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

private theorem symm_semi {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e) :
    IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [hs]
  simp

private theorem symm_int {ξ : Representation ℂ Γ V} {ξ' : Representation ℂ Γ V'} {e : V ≃+ V'}
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : ∀ g x, e.symm (ξ' g x) = ξ g (e.symm x) := by
  intro g x
  apply e.injective
  rw [hi]
  simp

private theorem forms_left {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (γ : Γ) (g : H) : φ.1 (ι γ * g) = ξ γ (φ.1 g) := φ.2.1 γ g

private theorem forms_right {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (k : H) (hk : k ∈ K) (g : H) : φ.1 (g * k) = φ.1 g := φ.2.2 k hk g

private def fmap (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x))
    (φ : HeckeTraceForms.forms ι K ξ) : HeckeTraceForms.forms ι K ξ' :=
  ⟨fun g => e (φ.1 g), fun γ g => by
      show e (φ.1 (ι γ * g)) = ξ' γ (e (φ.1 g))
      rw [forms_left φ, hi],
    fun k hk g => by
      show e (φ.1 (g * k)) = e (φ.1 g)
      rw [forms_right φ k hk]⟩

private def fequiv (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) :
    HeckeTraceForms.forms ι K ξ ≃+ HeckeTraceForms.forms ι K ξ' where
  toFun := fmap ι K e hi
  invFun := fmap ι K e.symm (symm_int hi)
  left_inv φ := by
    apply Subtype.ext; funext g
    exact e.symm_apply_apply _
  right_inv φ := by
    apply Subtype.ext; funext g
    exact e.apply_symm_apply _
  map_add' a b := by
    apply Subtype.ext; funext g
    exact map_add e _ _

private theorem fequiv_semi (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : IsSemi σ (fequiv ι K e hi) := by
  intro c φ
  apply Subtype.ext; funext g
  exact hs c (φ.1 g)

private theorem transport {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) {F : H → ℂ}
    {T : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (hT : HeckeTraceForms.IsHecke ι K ξ F T) :
    ∃ T' : HeckeTraceForms.forms ι K ξ' →ₗ[ℂ] HeckeTraceForms.forms ι K ξ',
      HeckeTraceForms.IsHecke ι K ξ' (fun h => σ (F h)) T' ∧
        ∀ x, fequiv ι K e hi (T x) = T' (fequiv ι K e hi x) := by
  have hsym := symm_semi (fequiv_semi ι K hs hi)
  refine ⟨{ toFun := fun ψ => fequiv ι K e hi (T ((fequiv ι K e hi).symm ψ))
            map_add' := fun a b => by simp
            map_smul' := fun c ψ => by
              rw [hsym c ψ, map_smul, fequiv_semi ι K hs hi]
              simp }, ?_, ?_⟩
  · intro ψ g
    change e ((T ((fequiv ι K e hi).symm ψ)).1 g) = _
    rw [hT, AddEquiv.map_finsum]
    refine finsum_congr fun q => ?_
    rw [hs]
    congr 1
    exact e.apply_symm_apply _
  · intro x
    change fequiv ι K e hi (T x) = fequiv ι K e hi (T ((fequiv ι K e hi).symm (fequiv ι K e hi x)))
    rw [AddEquiv.symm_apply_apply]

private theorem hecke_unique {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {F : H → ℂ}
    {T T' : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (h : HeckeTraceForms.IsHecke ι K ξ F T)
    (h' : HeckeTraceForms.IsHecke ι K ξ F T') : T = T' := by
  apply LinearMap.ext; intro φ
  apply Subtype.ext; funext g
  rw [h φ g, h' φ g]

end Transport

theorem heckeTraceSemi_of :
    TraceSemi → HeckeTraceSemi := by
  intro hTr σ Γ H V V' _ _ _ _ _ _ ξ ξ' e hs hi ι K F
  by_cases h : ∃ T, HeckeTraceForms.IsHecke ι K ξ F T
  · obtain ⟨T', hT', hint⟩ := transport (ι := ι) (K := K) hs hi h.choose_spec
    have h' : ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := ⟨T', hT'⟩
    have hc : h'.choose = T' := hecke_unique h'.choose_spec hT'
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dif_pos h, dif_pos h', hc]
    exact hTr σ _ _ (fequiv ι K e hi) (fequiv_semi ι K hs hi) _ _ hint
  · have h' : ¬ ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := by
      rintro ⟨T', hT'⟩
      obtain ⟨T, hT, -⟩ := transport (ι := ι) (K := K) (symm_semi hs) (symm_int hi) hT'
      refine h ⟨T, ?_⟩
      simpa only [RingEquiv.symm_apply_apply] using hT
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dif_neg h, dif_neg h', map_zero]

end UpperTheory.Gal.LocalSmoothExtension
