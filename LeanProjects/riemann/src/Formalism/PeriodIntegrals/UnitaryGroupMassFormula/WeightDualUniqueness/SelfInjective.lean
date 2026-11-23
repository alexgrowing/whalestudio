import Mathlib

namespace PI.UnitaryGroupMassFormula.AlgWtDualUniq

open Module

variable {G : Type*} [Group G] {Va Vb : Type*} [AddCommGroup Va] [Module ℂ Va] [AddCommGroup Vb] [Module ℂ Vb]
  (ρa : Representation ℂ G Va) (ρb : Representation ℂ G Vb)

def Inv (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) : Prop := ∀ g x y, B (ρa g x) (ρb g y) = B x y

def rKer (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) : Subrepresentation ρb where
  toSubmodule := LinearMap.ker B.flip
  apply_mem_toSubmodule g y hy := by
    rw [LinearMap.mem_ker] at hy ⊢
    ext x
    have h1 := hB g (ρa g⁻¹ x) y
    rw [Representation.self_inv_apply] at h1
    rw [LinearMap.flip_apply, h1, ← LinearMap.flip_apply, hy]
    rfl

def lKer (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) : Subrepresentation ρa where
  toSubmodule := LinearMap.ker B
  apply_mem_toSubmodule g x hx := by
    rw [LinearMap.mem_ker] at hx ⊢
    ext y
    have h1 := hB g x (ρb g⁻¹ y)
    rw [Representation.self_inv_apply] at h1
    rw [h1, hx]
    rfl

variable {ρa ρb}

theorem flip_injective [ρb.IsIrreducible] (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) :
    Function.Injective B.flip := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (rKer ρa ρb B hB) with h | h
  · have hk : LinearMap.ker B.flip = ⊥ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    exact LinearMap.ker_eq_bot.mp hk
  · exfalso
    apply h0
    have hk : LinearMap.ker B.flip = ⊤ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    ext x y
    have hy : y ∈ LinearMap.ker B.flip := by rw [hk]; trivial
    rw [LinearMap.mem_ker] at hy
    simpa using LinearMap.congr_fun hy x

theorem self_injective [ρa.IsIrreducible] (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) :
    Function.Injective B := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (lKer ρa ρb B hB) with h | h
  · have hk : LinearMap.ker B = ⊥ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    exact LinearMap.ker_eq_bot.mp hk
  · exfalso
    apply h0
    have hk : LinearMap.ker B = ⊤ := by
      exact (congrArg Subrepresentation.toSubmodule h).trans rfl
    ext x y
    have hx : x ∈ LinearMap.ker B := by rw [hk]; trivial
    rw [LinearMap.mem_ker] at hx
    simpa using LinearMap.congr_fun hx y

theorem finrank_eq [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) :
    finrank ℂ Vb = finrank ℂ (Dual ℂ Va) := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (flip_injective B hB h0)
  have h2 := LinearMap.finrank_le_finrank_of_injective (self_injective B hB h0)
  rw [Subspace.dual_finrank_eq] at h1 h2 ⊢
  omega

noncomputable def phi [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) : Vb ≃ₗ[ℂ] Dual ℂ Va :=
  LinearMap.linearEquivOfInjective B.flip (flip_injective B hB h0) (finrank_eq B hB h0)

theorem phi_apply [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) (y : Vb) (x : Va) :
    phi B hB h0 y x = B x y := rfl

theorem phi_equiv [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) (g : G) (y : Vb) (x : Va) :
    phi B hB h0 (ρb g y) x = phi B hB h0 y (ρa g⁻¹ x) := by
  rw [phi_apply, phi_apply]
  have h1 := hB g (ρa g⁻¹ x) y
  rw [Representation.self_inv_apply] at h1
  exact h1

theorem dual_unique {Vc : Type*} [AddCommGroup Vc] [Module ℂ Vc] {ρc : Representation ℂ G Vc}
    [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [FiniteDimensional ℂ Vc]
    [ρa.IsIrreducible] [ρb.IsIrreducible] [ρc.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0)
    (C : Va →ₗ[ℂ] Vc →ₗ[ℂ] ℂ) (hC : Inv ρa ρc C) (hC0 : C ≠ 0) :
    ∃ T : Vb ≃ₗ[ℂ] Vc, ∀ g y, T (ρb g y) = ρc g (T y) := by
  refine ⟨(phi B hB h0).trans (phi C hC hC0).symm, fun g y => ?_⟩
  apply (phi C hC hC0).injective
  ext x
  rw [phi_equiv C hC hC0 g]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [phi_equiv B hB h0 g]

end PI.UnitaryGroupMassFormula.AlgWtDualUniq
