import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PolFanReal

theorem bilin_eq_sum {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (β : LinearMap.BilinForm ℤ X) :
    β = ∑ j, ∑ k, β (Module.Free.chooseBasis ℤ X j) (Module.Free.chooseBasis ℤ X k) •
      (LinearMap.toMatrix₂ (Module.Free.chooseBasis ℤ X) (Module.Free.chooseBasis ℤ X)).symm (Matrix.single j k 1) := by
  apply (LinearMap.toMatrix₂ (Module.Free.chooseBasis ℤ X) (Module.Free.chooseBasis ℤ X)).injective
  simp only [map_sum, map_zsmul, LinearEquiv.apply_symm_apply]
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, LinearMap.toMatrix₂_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro k _ hk; simp [hk]
  · simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [hj]
  · simp

theorem linearForm_of_toReal_eq : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ) (be : LinearMap.BilinForm ℤ X),
    GlobalTheory.PolFan.toReal be = ∑ i, c i • GlobalTheory.PolFan.toReal (γ i) → ((ℓ be : ℤ) : ℝ) = ∑ i, c i * (ℓ (γ i) : ℝ) := by
  intro X _ _ _ ℓ m γ c be h
  set b := Module.Free.chooseBasis ℤ X
  set E := fun j k => (LinearMap.toMatrix₂ b b).symm (Matrix.single j k (1:ℤ))
  have key : ∀ β : LinearMap.BilinForm ℤ X, ((ℓ β : ℤ) : ℝ) = ∑ j, ∑ k, ((β (b j) (b k) : ℤ) : ℝ) * ((ℓ (E j k) : ℤ) : ℝ) := by
    intro β
    conv_lhs => rw [GlobalTheory.PolFanReal.bilin_eq_sum β]
    simp only [map_sum, map_zsmul, smul_eq_mul, Int.cast_sum, Int.cast_mul, E, b]
  have hjk : ∀ j k, ((be (b j) (b k) : ℤ) : ℝ) = ∑ i, c i * ((γ i (b j) (b k) : ℤ) : ℝ) := by
    intro j k
    have := congrArg (fun f => f (b j) (b k)) h
    simpa [GlobalTheory.PolFan.toReal, LinearMap.sum_apply, LinearMap.smul_apply] using this
  calc ((ℓ be : ℤ) : ℝ) = ∑ j, ∑ k, ((be (b j) (b k) : ℤ) : ℝ) * ((ℓ (E j k) : ℤ) : ℝ) := key be
    _ = ∑ j, ∑ k, ∑ i, c i * ((γ i (b j) (b k) : ℤ) : ℝ) * ((ℓ (E j k) : ℤ) : ℝ) := by
      simp_rw [hjk, Finset.sum_mul]
    _ = ∑ i, c i * ∑ j, ∑ k, ((γ i (b j) (b k) : ℤ) : ℝ) * ((ℓ (E j k) : ℤ) : ℝ) := by
      simp_rw [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ = ∑ i, c i * (ℓ (γ i) : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [key (γ i)]

end GlobalTheory.PolFanReal
