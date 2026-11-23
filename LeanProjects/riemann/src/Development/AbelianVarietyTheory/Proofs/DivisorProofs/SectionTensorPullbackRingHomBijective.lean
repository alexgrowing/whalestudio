import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaApplyEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem theta_bijective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (U : T.affineOpens) :
    Function.Bijective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have P₁ := CommRingCat.isPushout_tensorProduct A Γ(T, U) B
  have P₂ : IsPushout (CommRingCat.ofHom (algebraMap A Γ(T, U)))
      (CommRingCat.ofHom (algebraMap A B))
      ((pullback.snd (str A B) g).app U)
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (pullback.fst (str A B) g).appLE ⊤ W (by simp)) := by
    refine po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of B)) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← Iso.inv_comp_eq]; rfl
    · have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
      rw [← h1, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    · rw [Scheme.Hom.app_eq_appLE]; rfl
    · simp
  have e : CommRingCat.ofHom (theta A B g U) = (P₁.isoIsPushout _ _ P₂).hom := by
    apply P₁.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]
      ext c
      have := theta_tmul A B g U c 1
      simp only [map_one, mul_one] at this
      exact this
    · rw [IsPushout.inr_isoIsPushout_hom]
      ext b
      have := theta_tmul A B g U 1 b
      simp only [map_one, one_mul] at this
      exact this
  have : IsIso (CommRingCat.ofHom (theta A B g U)) := by rw [e]; infer_instance
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (theta A B g U))

end GlobalTheory.HilbAff
