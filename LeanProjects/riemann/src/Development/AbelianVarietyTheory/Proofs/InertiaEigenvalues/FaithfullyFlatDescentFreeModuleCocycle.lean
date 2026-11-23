import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange

open TensorProduct

namespace GlobalTheory.CocycleDescent

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d : ℕ}

noncomputable def defect (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) :
    (Fin d → B) →ₗ[A] (Fin d → B ⊗[A] B) :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap.compLeft (Fin d) -
    (ε.mulVecLin.restrictScalars A) ∘ₗ
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap.compLeft (Fin d)

theorem defect_apply (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (z : Fin d → B) :
    defect ε z = (fun i => z i ⊗ₜ[A] (1 : B)) - ε.mulVec fun i => (1 : B) ⊗ₜ[A] z i := rfl

theorem lTensor_defect (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (x : B ⊗[A] (Fin d → B)) :
    piRight A A B (fun _ : Fin d => B ⊗[A] B) ((defect ε).lTensor B x) =
      (fun i => Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
          (piRight A A B (fun _ : Fin d => B) x i)) -
      (ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))).mulVec
        (fun i => Algebra.TensorProduct.map (AlgHom.id A B)
          (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
            (piRight A A B (fun _ : Fin d => B) x i)) := by
  induction x with
  | zero =>
    ext i
    simp [Matrix.mulVec, dotProduct]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply, map_add, mul_add,
      Finset.sum_add_distrib]
    abel
  | tmul b z =>
    ext i
    simp [defect_apply, Matrix.mulVec, dotProduct, tmul_sub, tmul_sum]

theorem isBaseChange [Module.Flat A B] (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (hε : IsUnit ε)
    (hc : ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) *
      ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) =
      ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B))) :
    IsBaseChange B (LinearMap.ker (defect ε)).subtype := by
  set N := LinearMap.ker (defect ε) with hN
  set e := piRight A A B (fun _ : Fin d => B) with he
  have hεinj : Function.Injective ε.mulVec := Matrix.mulVec_injective_of_isUnit hε
  have key : ∀ x : B ⊗[A] N, (fun i => (N.subtype.liftBaseChange B x) i ⊗ₜ[A] (1 : B)) =
      ε.mulVec (e (N.subtype.lTensor B x)) := by
    intro x
    induction x with
    | zero => ext i; simp
    | add x y hx hy =>
      rw [map_add, map_add, map_add, Matrix.mulVec_add, ← hx, ← hy]
      ext i
      simp [add_tmul]
    | tmul b n =>
      have hn : defect ε n.1 = 0 := n.2
      rw [defect_apply, sub_eq_zero] at hn
      have h1 : e (N.subtype.lTensor B (b ⊗ₜ n)) =
          (b ⊗ₜ[A] (1 : B)) • fun i => (1 : B) ⊗ₜ[A] n.1 i := by
        ext i
        simp [he]
      rw [h1, Matrix.mulVec_smul, ← hn]
      ext i
      simp
  have hleft : ∀ z w : Fin d → B,
      (fun i => z i ⊗ₜ[A] (1 : B)) = (fun i => w i ⊗ₜ[A] (1 : B)) → z = w := by
    intro z w h
    ext i
    simpa using congrArg (Algebra.TensorProduct.lmul' A (S := B)) (congrFun h i)
  change Function.Bijective (N.subtype.liftBaseChange B)
  constructor
  · intro x y hxy
    have h := key x
    rw [hxy, key y] at h
    exact (Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
      (e.injective (hεinj h))).symm
  · intro z
    obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hε (fun i => z i ⊗ₜ[A] (1 : B))
    have hex := Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map (defect ε))
    have h0 : (defect ε).lTensor B (e.symm y) = 0 := by
      apply (piRight A A B (fun _ : Fin d => B ⊗[A] B)).injective
      rw [lTensor_defect, map_zero, sub_eq_zero, ← he, e.apply_symm_apply]
      set i₁₂ := Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) with h12
      set i₁₃ := Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) with h13
      have hu : IsUnit (ε.map i₁₂) := hε.map (i₁₂.toRingHom.mapMatrix)
      apply Matrix.mulVec_injective_of_isUnit hu
      rw [Matrix.mulVec_mulVec, hc]
      ext i
      have a := RingHom.map_mulVec i₁₂.toRingHom ε y i
      have b := RingHom.map_mulVec i₁₃.toRingHom ε y i
      refine a.symm.trans (Eq.trans ?_ b)
      rw [hy]
      simp [h12, h13, ← Algebra.TensorProduct.one_def]
    obtain ⟨x, hx⟩ := (hex _).mp h0
    refine ⟨x, hleft _ _ ?_⟩
    rw [key, ← hy]
    congr 1
    rw [← e.apply_symm_apply y, ← hx]

theorem descent (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (d : ℕ) (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (hε : IsUnit ε)
    (hc : ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) *
      ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) =
      ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)))
    (N : Submodule A (Fin d → B))
    (hN : ∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε.mulVec fun i => (1 : B) ⊗ₜ[A] z i) :
    Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  have hk : N = LinearMap.ker (defect ε) := by
    ext z
    rw [hN, LinearMap.mem_ker, defect_apply, sub_eq_zero]
  have hb : IsBaseChange B N.subtype := hk ▸ isBaseChange ε hε hc
  have : Module.Finite B (B ⊗[A] N) := Module.Finite.equiv hb.equiv.symm
  have : Module.Projective B (B ⊗[A] N) := Module.Projective.of_equiv hb.equiv.symm
  exact ⟨GlobalTheory.Descent.finite B, GlobalTheory.Descent.projective B, hb⟩

end GlobalTheory.CocycleDescent
