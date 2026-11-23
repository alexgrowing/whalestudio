import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaApplyEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HilbAff

theorem bc_appLE_comp_psi : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.Opens), letI := (GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra; ∀ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U → ((GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤ ((pullback.snd (GlobalTheory.HilbAff.str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp)).hom.comp (GlobalTheory.HilbAff.psi A B C) = (GlobalTheory.HilbAff.theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
  intro A B C _ _ _ _ _ Z h U
  letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
  intro φ hφ
  have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have hpsi : ∀ (c : C) (b : B), psi A B C (c ⊗ₜ[A] b) =
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
    intro c b
    have h1 := congrArg (fun F => F.hom b) eL
    have h2 := congrArg (fun F => F.hom c) eR
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
    rw [h1, h2, ← map_mul, ← map_mul]
    simp [psi]
  have eF : (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      (pullback.fst (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
  have eS : (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      h.appLE ⊤ U (by simp) ≫
        (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) ≫ h)
      (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
    rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c b =>
    have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
    have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
    have hc : φ c = secAlg C h U c := congrArg (fun f => f c) hφ
    rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      theta_tmul, hc, secAlg, RingHom.comp_apply, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.HilbAff
