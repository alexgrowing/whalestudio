import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_le_pow_card_of_ultrametric :
    ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I]
      (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) →
      ‖M.det‖ ≤ r ^ Fintype.card I := by
  intro A _ _ I _ _ M r hr hM
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _) ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h2 : ‖∏ i, M (σ i) i‖ ≤ r ^ Fintype.card I := by
    rw [norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : I, r :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
      _ = r ^ Fintype.card I := by simp
  calc _ ≤ 1 * r ^ Fintype.card I :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.CompanionTheory.Ar.Fl
