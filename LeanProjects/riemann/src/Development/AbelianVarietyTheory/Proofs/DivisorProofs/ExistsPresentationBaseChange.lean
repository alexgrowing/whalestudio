import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain

set_option autoImplicit false

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.RingChain

theorem exists_quot_equiv_of_section {A F L : Type} [CommRing A] [AddCommGroup F] [Module A F] [AddCommGroup L] [Module A L]
    (φ : F →ₗ[A] L) (σ : L →ₗ[A] F) (h : ∀ l, φ (σ l) = l) (c : A) (R : F →ₗ[A] F)
    (hR : ∀ x, R x = x - σ (φ x) + c • σ (φ x)) :
    ∃ e : (F ⧸ LinearMap.range R) ≃ₗ[A] L ⧸ c • (⊤ : Submodule A L),
      ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ x) := by
  have hs : Function.Surjective ((c • (⊤ : Submodule A L)).mkQ ∘ₗ φ) :=
    (Submodule.mkQ_surjective _).comp fun l => ⟨σ l, h l⟩
  have hk : LinearMap.range R = LinearMap.ker ((c • (⊤ : Submodule A L)).mkQ ∘ₗ φ) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨φ z, trivial, by rw [hR, map_add, map_sub, map_smul, h, sub_self, zero_add]⟩
    · rintro ⟨l, -, hl⟩
      refine ⟨x - σ (φ x) + σ l, ?_⟩
      rw [hR, map_add, map_sub, h, h, sub_self, zero_add, ← map_smul, hl]
      abel
  exact ⟨(Submodule.quotEquivOfEq _ _ hk).trans (LinearMap.quotKerEquivOfSurjective _ hs), fun _ => rfl⟩

theorem exists_presentation_baseChange : ∀ (A : Type) [CommRing A] (c : A) (Lie : Type) [AddCommGroup Lie] [Module A Lie] [Module.Finite A Lie] [Module.Projective A Lie], ∃ (m₁ r₁ : ℕ) (y : Fin m₁ → Lie) (R : Matrix (Fin m₁) (Fin r₁) A), ∀ (A' : Type) [CommRing A'] [Algebra A A'] (Lie' : Type) [AddCommGroup Lie'] [Module A' Lie'] (eL : A' ⊗[A] Lie ≃ₗ[A'] Lie') (c' : A') (R₁' : Matrix (Fin m₁) (Fin r₁) A'), c' = algebraMap A A' c → R₁' = R.map (algebraMap A A') → ∃ e : ((Fin m₁ → A') ⧸ LinearMap.range (Matrix.mulVecLin R₁')) ≃ₗ[A'] Lie' ⧸ c' • (⊤ : Submodule A' Lie'), ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (∑ i, x i • eL (1 ⊗ₜ y i)) := by
  intro A _ c Lie _ _ _ _
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A Lie
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let y : Fin m → Lie := fun i => π (Pi.single i 1)
  let E : Matrix (Fin m) (Fin m) A := Matrix.of fun i j => s (y j) i
  have hy : ∀ l, ∑ i, s l i • y i = l := fun l => by
    have h1 : π (s l) = l := LinearMap.congr_fun hs l
    conv_rhs => rw [← h1, ← Finset.univ_sum_single (s l), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  refine ⟨m, m, y, 1 - E + c • E, ?_⟩
  intro A' _ _ Lie' _ _ eL c' R' hc hR
  let φ : (Fin m → A') →ₗ[A'] Lie' := Fintype.linearCombination A' fun i => eL (1 ⊗ₜ y i)
  let s' : Lie →ₗ[A] (Fin m → A') := LinearMap.pi fun i => Algebra.linearMap A A' ∘ₗ LinearMap.proj i ∘ₗ s
  let σ : Lie' →ₗ[A'] (Fin m → A') := s'.liftBaseChange A' ∘ₗ eL.symm.toLinearMap
  have hσ : ∀ l i, σ (eL (1 ⊗ₜ l)) i = algebraMap A A' (s l i) := fun l i => by
    simp [σ, s']
  have hφ : ∀ x, φ x = ∑ i, x i • eL (1 ⊗ₜ y i) := fun x => Fintype.linearCombination_apply _ _ _
  have h1 : ∀ l, φ (σ (eL (1 ⊗ₜ l))) = eL (1 ⊗ₜ l) := fun l => by
    rw [hφ]
    conv_rhs => rw [← hy l, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hσ, ← map_smul, TensorProduct.tmul_smul, algebraMap_smul]
  have h : ∀ l, φ (σ l) = l := fun l => by
    obtain ⟨t, rfl⟩ := eL.surjective l
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a l =>
      rw [show a ⊗ₜ[A] l = a • ((1 : A') ⊗ₜ[A] l) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, map_smul, h1]
  have hE : ∀ x, σ (φ x) = (E.map (algebraMap A A')).mulVec x := fun x => by
    funext i
    rw [hφ, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, hσ, smul_eq_mul, mul_comm]
    rfl
  have hR' : R' = 1 - E.map (algebraMap A A') + c' • E.map (algebraMap A A') := by
    subst hR hc
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Algebra.smul_def (A := A')]
  obtain ⟨e, he⟩ := exists_quot_equiv_of_section φ σ h c' (Matrix.mulVecLin R') fun x => by
    rw [hE, hR', Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  exact ⟨e, fun x => by rw [he, hφ]⟩

end GlobalTheory.RingChain
