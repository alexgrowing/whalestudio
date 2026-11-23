import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegralityStatement

set_option autoImplicit false

namespace GlobalTheory.DegCmp

open Polynomial

theorem le_sqrt_mul_pow_of_sq_le {n : ℕ} (τ : ℕ) (x y C : ℝ) (u : Fin n → ℝ) (hx : 0 ≤ x) (hu : ∀ i, 0 ≤ u i)
    (h : y ^ 2 ≤ C * (∑ i, u i ^ 2) ^ τ) :
    x ^ τ * y ≤ Real.sqrt (max C 0) * (1 + ∑ i, x * u i) ^ τ := by
  have hS : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu i
  have h1 : ∑ i, u i ^ 2 ≤ (∑ i, u i) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hu i
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : y ^ 2 ≤ (Real.sqrt (max C 0) * (∑ i, u i) ^ τ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm τ 2, pow_mul]
    exact h.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 h1 τ) (pow_nonneg h0 τ) (le_max_right _ _))
  have h3 : y ≤ Real.sqrt (max C 0) * (∑ i, u i) ^ τ :=
    (abs_le_of_sq_le_sq' h2 (by positivity)).2
  calc x ^ τ * y ≤ x ^ τ * (Real.sqrt (max C 0) * (∑ i, u i) ^ τ) := by gcongr
    _ = Real.sqrt (max C 0) * (∑ i, x * u i) ^ τ := by rw [← Finset.mul_sum, mul_pow]; ring
    _ ≤ Real.sqrt (max C 0) * (1 + ∑ i, x * u i) ^ τ := by
      have : 0 ≤ ∑ i, x * u i := Finset.sum_nonneg fun i _ => mul_nonneg hx (hu i)
      gcongr
      linarith

theorem isIntDeg_of_bounded_of_algHom (K V Ω R : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] (ι : R →ₐ[K] Ω) (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V)
    (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ) (hw : ∀ i, ι (w' i) = (a : Ω) * ev (w i))
    (ht : ι t' = (a : Ω) ^ τ * t)
    (hb : ∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) :
    IsIntDeg ev τ t := by
  have hint : IsIntegral (Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)))
      (X ^ τ * Polynomial.C t' : Polynomial R) := by
    refine GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.2.2 K (Polynomial R) σ n τ _ _ (Real.sqrt (max C 0)) fun φ hφ => ?_
    have h := hb (φ.comp Polynomial.C) hφ
    simp only [map_mul, map_pow, norm_mul, norm_pow]
    exact le_sqrt_mul_pow_of_sq_le τ _ _ C (fun i => ‖φ (Polynomial.C (w' i))‖) (norm_nonneg _)
      (fun _ => norm_nonneg _) h
  let f : Polynomial R →ₐ[K] Polynomial Ω :=
    Polynomial.eval₂AlgHom ((Polynomial.CAlgHom : Ω →ₐ[K] Polynomial Ω).comp ι) (X * Polynomial.C ((a⁻¹ : Ωˣ) : Ω))
      fun _ => Commute.all _ _
  have hfX : f X = X * Polynomial.C ((a⁻¹ : Ωˣ) : Ω) := by simp [f]
  have hfC : ∀ b : R, f (Polynomial.C b) = Polynomial.C (ι b) := fun b => by simp [f]
  have hfw : ∀ i, f (X * Polynomial.C (w' i)) = X * Polynomial.C (ev (w i)) := fun i => by
    rw [map_mul, hfX, hfC, hw, mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hft : f (X ^ τ * Polynomial.C t') = X ^ τ * Polynomial.C t := by
    rw [map_mul, map_pow, hfX, hfC, ht, mul_pow, mul_assoc, ← map_pow, ← map_mul, ← mul_assoc, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  have hmem : ∀ x ∈ Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)), f x ∈ coneAlg ev := by
    intro x hx
    have : Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)) ≤ (coneAlg ev).comap f := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, rfl⟩
      change f _ ∈ coneAlg ev
      rw [hfw]
      exact Algebra.subset_adjoin ⟨w i, rfl⟩
    exact this hx
  rw [IsIntDeg, ← hft]
  exact hint.map_of_comp_eq
    ((f.toRingHom.comp (Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R))).val.toRingHom).codRestrict
      (coneAlg ev) fun x => hmem x.1 x.2) f.toRingHom (RingHom.ext fun _ => rfl)

theorem isIntDeg_of_bounded (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (R : Subalgebra K Ω) [Algebra.FiniteType K R] (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V)
    (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ) (hw : ∀ i, (w' i : Ω) = (a : Ω) * ev (w i))
    (ht : (t' : Ω) = (a : Ω) ^ τ * t)
    (hb : ∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) :
    IsIntDeg ev τ t :=
  isIntDeg_of_bounded_of_algHom K V Ω R ev R.val σ a n τ w w' t t' C hw ht hb

end GlobalTheory.DegCmp
