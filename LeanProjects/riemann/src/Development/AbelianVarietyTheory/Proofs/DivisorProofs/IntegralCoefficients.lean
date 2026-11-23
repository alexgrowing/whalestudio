import Mathlib

namespace GlobalTheory.NonzeroDeterminantIntegrality

open Matrix

theorem exists_det_ne_zero {K I Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (v : I → Λ → K)
    (h : ∀ c : Λ → K, (∀ i, ∑ l, c l * v i l = 0) → c = 0) :
    ∃ f : Λ → I, (Matrix.of fun a l => v (f a) l).det ≠ 0 := by
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hexp : ∀ x : Λ → K, φ x = ∑ l, φ (Pi.single l 1) * x l := by
      intro x
      conv_lhs => rw [pi_eq_sum_univ' x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hc := h (fun l => φ (Pi.single l 1)) (fun i => by
      rw [← hexp]
      exact hle (Submodule.subset_span ⟨i, rfl⟩))
    apply hφ
    refine LinearMap.ext fun x => ?_
    rw [hexp]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := congrFun hc l
    simp only [Pi.zero_apply] at this
    rw [this, zero_mul]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Λ → K) := Module.Basis.mk hli (by rw [hsp, hspan])
  let e : Λ ≃ κ := (Pi.basisFun K Λ).indexEquiv b
  refine ⟨fun l => a (e l), ?_⟩
  have hli' : LinearIndependent K (Matrix.of fun x l => v (a (e x)) l).row :=
    hli.comp e e.injective
  have := Matrix.linearIndependent_rows_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp this).ne_zero

theorem integral_coefficients : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁]
    (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a : W, i₁ a ≠ 0 → IsUnit a) →
    ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W),
    (∀ c : Λ → K₁, (∀ i : I, ∑ l : Λ, c l * i₁ (u i l) = 0) → c = 0) →
    ∀ (w : I → W) (z : Λ → K₀), (∀ i : I, i₀ (w i) = ∑ l : Λ, z l * i₀ (u i l)) →
    ∃ z₀ : Λ → W, (∀ l : Λ, i₀ (z₀ l) = z l) ∧ ∀ i : I, w i = ∑ l : Λ, z₀ l * u i l := by
  intro W _ _ K₀ K₁ _ _ i₀ i₁ hinj hunit I Λ _ u hu w z hz
  classical
  obtain ⟨f, hf⟩ := exists_det_ne_zero (fun i l => i₁ (u i l)) hu
  let M : Matrix Λ Λ W := Matrix.of fun a l => u (f a) l
  have hdet : IsUnit M.det := by
    apply hunit
    rw [RingHom.map_det]
    exact hf
  let z₀ : Λ → W := M⁻¹ *ᵥ (fun a => w (f a))
  have hM : M *ᵥ z₀ = fun a => w (f a) := by
    simp only [z₀]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hdet₀ : IsUnit (i₀.mapMatrix M).det := by
    rw [← RingHom.map_det]
    exact hdet.map i₀
  have key : (fun l => i₀ (z₀ l)) = z := by
    apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hdet₀)
    funext a
    have h1 := congrArg i₀ (congrFun hM a)
    rw [hz] at h1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1 ⊢
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨z₀, fun l => congrFun key l, fun i => hinj ?_⟩
  rw [hz, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← congrFun key l]

end GlobalTheory.NonzeroDeterminantIntegrality
