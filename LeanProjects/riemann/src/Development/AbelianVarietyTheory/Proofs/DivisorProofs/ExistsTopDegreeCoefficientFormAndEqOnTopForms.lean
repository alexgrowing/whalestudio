import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isTop_exists_and_eq (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) :
    IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧
      ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  intro h
  refine ⟨h.exists_isTop, fun τ hτ y hy => ?_⟩
  obtain ⟨b, hb⟩ := h.exists_basis
  set u : Fin d → K := fun j => (algebraMap F K (x j.succ / x 0))⁻¹
  have hu : ∀ j, u j ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  have hp : (∏ j, u j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hu j
  have hv : vol0 k K x = (∏ j, u j) • ExteriorAlgebra.ιMulti K d b := by
    rw [← AlternatingMap.map_smul_univ]
    simp only [vol0, hb, u]

  have key : ∀ c : K, c • vol0 k K x = τ (c • vol0 k K x) • vol0 k K x := by
    intro c
    rw [map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have e : ExteriorAlgebra.ιMulti K d m = (b.det m * (∏ j, u j)⁻¹) • vol0 k K x := by
      rw [hv, smul_smul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
      intro φ
      have h2 := congrArg (fun g => g m)
        (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)))
      simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h2
      rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_self]
    rw [e]
    exact key _
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, add_smul, ← ha, ← hc]
  | smul r a _ ha => rw [map_smul, smul_eq_mul, mul_smul, ← ha]

end GlobalTheory.PD
