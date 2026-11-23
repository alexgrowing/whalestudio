import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.galMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  intro A R C O _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy htf σ
  set b := algebraMap R C (algebraMap A R a) with hb
  have key : ∀ c : C, ∑ i, T (y i * c) • x i = b * c := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i; rw [Algebra.smul_def, hT, mul_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, mul_assoc]
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hxy]
    simp
  let L := LinearMap.lTensor O (LinearMap.mulLeft R b)
  have hL : Function.Injective L := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact htf a ha c (by rw [Algebra.smul_def]; simpa using hc)
  let Φ : (G → O) → O ⊗[R] C := fun f => ∑ i, (∑ g, σ (act g (y i)) * f g) ⊗ₜ x i
  have hΦ : ∀ m, Φ (GlobalTheory.GoodEtale.galMap act σ m) = L m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp [Φ]
    | tmul o c =>
      simp only [Φ, GlobalTheory.GoodEtale.galMap_tmul, L, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply]
      have h2 : ∀ i, (∑ g, σ (act g (y i)) * (o * σ (act g c))) = T (y i * c) • o := by
        intro i
        rw [Algebra.smul_def, ← σ.commutes, hT, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, map_mul]; ring
      simp_rw [h2, ← key, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    | add m m' hm hm' =>
      rw [map_add, map_add, ← hm, ← hm']
      simp only [Φ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]
  rw [injective_iff_map_eq_zero]
  intro m hm
  apply hL
  rw [← hΦ, hm, map_zero]
  simp [Φ]
