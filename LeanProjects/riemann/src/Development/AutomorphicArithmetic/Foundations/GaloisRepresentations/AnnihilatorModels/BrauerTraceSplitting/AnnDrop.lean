import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts

noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison.Br

theorem annDrop : AnnDrop := by
  intro F G B C _ _ _ _ _ _ σ φ s ψ e hσ hφ hψ V _ _ V₀ _ _ i act ρ hρ f q n N A T hT hrel x hx
  rw [mem_Dinv] at hx
  have hpow : ∀ (m : ℕ) (b : B), e ((φ.toLinearMap ^ m) b) = (ψ.toLinearMap ^ m) (e b) := by
    intro m
    induction m with
    | zero => intro b; simp
    | succ m ih =>
      intro b
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact hφ _
  let Φ : V₀ ⊗[F] B ≃ₗ[F] V ⊗[F] C := TensorProduct.congr i.symm e.toLinearEquiv
  have hcomm : ∀ (a : End F V₀) (a' : End F V) (b : End F B) (b' : End F C),
      (∀ v, i.symm (a v) = a' (i.symm v)) → (∀ y, e (b y) = b' (e y)) →
      ∀ z, Φ (AlgebraTensorModule.map a b z) = TensorProduct.map a' b' (Φ z) := by
    intro a a' b b' ha hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v y =>
      simp only [Φ, AlgebraTensorModule.map_tmul, TensorProduct.congr_tmul, TensorProduct.map_tmul]
      rw [ha v]
      congr 1
      exact hb y
    | add u w hu hw => simp only [map_add, hu, hw]
  have hinv : ∀ g, TensorProduct.map (act g) (s g).toLinearMap (Φ x) = Φ x := by
    intro g
    rw [← hcomm (ρ g) (act g) (σ g) (s g).toLinearMap ?_ (hσ g) x, hx g]
    intro v
    have h := hρ g (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  have hsum := hrel (Φ x) hinv
  have hinj : Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (ψ.toLinearMap ^ (f * N))) := by
    have h0 : Function.Injective (ψ.toLinearMap ^ (f * N)) := by
      rw [Module.End.coe_pow]
      exact Function.Injective.iterate hψ _
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ h0
  have hz : ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) •
      TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j))) (Φ x) = 0 := by
    apply hinj
    rw [map_zero, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, ← Module.End.mul_eq_comp,
      ← pow_add]
    congr 3
    ring
  apply Φ.injective
  rw [map_zero, map_sum, Finset.sum_range, ← hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  rw [hcomm (T j) (A j) ((φ.toLinearMap ^ f) ^ (n - (j : ℕ))) (ψ.toLinearMap ^ (f * (n - j))) ?_ ?_ x]
  · intro v
    have h := hT j (i.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  · intro y
    rw [← pow_mul]
    exact hpow _ y

end UpperTheory.Gal.crystallineComparison.Br
