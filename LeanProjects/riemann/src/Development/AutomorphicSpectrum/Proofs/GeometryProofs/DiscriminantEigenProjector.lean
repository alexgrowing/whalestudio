import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ScaledCasimir

section General

variable {J A : Type*} [Fintype J] [DecidableEq J] [CommRing A] (a : Module.Basis J ℤ A)

noncomputable def dualScaled (m : J) : A :=
  ∑ n, (Algebra.traceMatrix ℤ a).adjugate m n • a n

theorem trace_dualScaled_mul_basis (m p : J) :
    Algebra.trace ℤ A (dualScaled a m * a p) =
      if m = p then (Algebra.traceMatrix ℤ a).det else 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul (Algebra.traceMatrix ℤ a)) m) p
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one,
    mul_zero] at h
  rw [← h]
  simp only [dualScaled, Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem trace_dualScaled_mul (m : J) (y : A) :
    Algebra.trace ℤ A (dualScaled a m * y) = a.repr y m * (Algebra.traceMatrix ℤ a).det := by
  conv_lhs => rw [← a.sum_repr y]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, trace_dualScaled_mul_basis,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem eq_of_trace_mul_basis (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) {x y : A}
    (H : ∀ p, Algebra.trace ℤ A (x * a p) = Algebra.trace ℤ A (y * a p)) : x = y := by
  have hz : (fun q => a.repr (x - y) q) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hd
    funext p
    have h1 : Algebra.trace ℤ A ((x - y) * a p) = 0 := by
      rw [sub_mul, map_sub, H p, sub_self]
    conv at h1 => lhs; rw [← a.sum_repr (x - y)]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul] at h1
    simpa [Matrix.vecMul, dotProduct, Algebra.traceMatrix_apply, Algebra.traceForm_apply] using h1
  have : x - y = 0 := by
    apply a.repr.injective
    ext q
    simpa using congrFun hz q
  exact sub_eq_zero.mp this

theorem mul_dualScaled (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) (b : A) (n : J) :
    b * dualScaled a n = ∑ m, a.repr (b * a m) n • dualScaled a m := by
  apply eq_of_trace_mul_basis a hd
  intro p
  have h1 : b * dualScaled a n * a p = dualScaled a n * (b * a p) := by ring
  rw [h1, trace_dualScaled_mul]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, trace_dualScaled_mul,
    Module.Basis.repr_self, smul_eq_mul]
  simp [Finsupp.single_apply]

theorem sum_dualScaled_mul (hd : (Algebra.traceMatrix ℤ a).det ≠ 0) :
    ∑ m, dualScaled a m * a m = (((Algebra.traceMatrix ℤ a).det : ℤ) : A) := by
  apply eq_of_trace_mul_basis a hd
  intro k
  have h1 : ∀ m, dualScaled a m * a m * a k = dualScaled a m * (a k * a m) := fun m => by ring
  have h2 : (((Algebra.traceMatrix ℤ a).det : ℤ) : A) * a k =
      (Algebra.traceMatrix ℤ a).det • a k := by rw [zsmul_eq_mul]
  rw [Finset.sum_mul, map_sum, h2, map_zsmul, Algebra.trace_eq_matrix_trace a (a k)]
  simp only [h1, trace_dualScaled_mul, Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem equivariant (hd : (Algebra.traceMatrix ℤ a).det ≠ 0)
    {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (ρ : A →+* Module.End Ω V) (σ : A →+* Ω) (b : A) (v : V) :
    ρ b (∑ m, σ (dualScaled a m) • ρ (a m) v) =
      σ b • ∑ m, σ (dualScaled a m) • ρ (a m) v := by
  have hmul : ∀ m, ρ b (ρ (a m) v) = ∑ n, ((a.repr (b * a m) n : ℤ) : Ω) • ρ (a n) v := by
    intro m
    have h0 : ρ b (ρ (a m) v) = ρ (b * a m) v := by simp [map_mul]
    rw [h0]
    conv_lhs => rw [← a.sum_repr (b * a m)]
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have hc : ∀ n, σ b * σ (dualScaled a n) =
      ∑ m, σ (dualScaled a m) * ((a.repr (b * a m) n : ℤ) : Ω) := by
    intro n
    rw [← map_mul, mul_dualScaled a hd, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc n, Finset.sum_smul]

end General

theorem exists_scaledCasimir :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (n : ℕ) (a c : Fin n → 𝓞 F), (∑ m, c m * a m = (((NumberField.discr F : ℤ) : 𝓞 F))) ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 F →+* Module.End Ω V) (σ : 𝓞 F →+* Ω) (b : 𝓞 F) (v : V), ρ b (∑ m, σ (c m) • ρ (a m) v) = σ b • ∑ m, σ (c m) • ρ (a m) v := by
  intro F _ _
  let a := Module.finBasis ℤ (𝓞 F)
  have hdet : (Algebra.traceMatrix ℤ a).det = NumberField.discr F := by
    rw [← Algebra.discr_def, NumberField.discr_eq_discr]
  have hd : (Algebra.traceMatrix ℤ a).det ≠ 0 := by
    rw [hdet]; exact NumberField.discr_ne_zero F
  refine ⟨_, a, dualScaled a, ?_, ?_⟩
  · rw [sum_dualScaled_mul a hd, hdet]
  · intro Ω _ V _ _ ρ σ b v
    exact equivariant a hd ρ σ b v

end GlobalTheory.CompanionTheory.Ar.ScaledCasimir
