import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem isAffineOpen_preimage_and_tensor_equiv_of_isPullback : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  intro k K _ _ _ X X' f f' π h V hV
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  refine ⟨hV.preimage π, ?_⟩
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := π ⁻¹ᵁ V) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have hpo' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top)
      (CommRingCat.ofHom (algebraMap k K)) (π.app V)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  letI : Algebra K Γ(X', π ⁻¹ᵁ V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X', π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  letI : Algebra k Γ(X', π ⁻¹ᵁ V) :=
    ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom).comp
      (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k Γ(X, V) Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun r => by
    exact (congrArg (fun φ => φ.hom r) hpo'.w).symm
  haveI : Algebra.IsPushout k K Γ(X, V) Γ(X', π ⁻¹ᵁ V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo'.flip
  refine ⟨(Algebra.IsPushout.equiv k K Γ(X, V) Γ(X', π ⁻¹ᵁ V)).toRingEquiv, fun a => ?_, fun c => ?_⟩
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]

end GlobalTheory
