import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem dualNumber_map_flat_surjective : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ ψ : DualNumber k →+* DualNumber K, ψ.comp (dnInl k) = (dnInl K).comp φ ∧ (dnFst K).comp ψ = φ.comp (dnFst k) ∧ Flat (spMap ψ) ∧ Surjective (spMap ψ) := by
  intro k K _ _ φ
  letI : Algebra k K := φ.toAlgebra
  let ψ₀ : DualNumber k →ₐ[k] DualNumber K :=
    DualNumber.lift ⟨(Algebra.ofId k (DualNumber K), DualNumber.eps),
      by simp, fun _ ↦ Commute.all _ _⟩
  have hψ₀ : ∀ x : DualNumber k, ψ₀ x = TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd) := by
    intro x
    rw [DualNumber.lift_apply_apply]
    ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let j : K →ₐ[k] DualNumber K := TrivSqZeroExt.inlAlgHom k K K
  let g : TensorProduct k (DualNumber k) K →ₐ[k] DualNumber K :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber K → TensorProduct k (DualNumber k) K := fun x ↦
    (1 : DualNumber k) ⊗ₜ[k] x.fst + (DualNumber.eps : DualNumber k) ⊗ₜ[k] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, g (h x) = x := by
    intro x
    simp only [h, g, map_add, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀]
  have hhg : ∀ x, h (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber k) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[k] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add, hadd, hx, hy]
  have hbij : Function.Bijective g := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  refine ⟨ψ₀.toRingHom, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [hψ₀, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  · refine RingHom.ext fun x ↦ ?_
    simp [hψ₀]
  · have hc : ψ₀.toRingHom = g.toRingHom.comp (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)) := by
      refine RingHom.ext fun x ↦ ?_
      simp [g, j, Algebra.TensorProduct.algebraMap_apply]
    have hff : (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
    have h1 := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)))).2 hff
    have := h1.1
    have := h1.2
    let eR : TensorProduct k (DualNumber k) K ≃+* DualNumber K := (AlgEquiv.ofBijective g hbij).toRingEquiv
    have hi : IsIso (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map eR.toCommRingCatIso.hom))
    rw [hc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.DualOpen
