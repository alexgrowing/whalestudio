import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolution
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulOfSeparableGenerated
open GlobalTheory.UnitLemma Polynomial Matrix

noncomputable section

namespace GlobalTheory.InertUnitOrb

theorem stdH_mulVec_eq_of_unitary {K : UQ} {n : ℕ} (u : Matrix (Fin n) (Fin n) K.E)
    (hu : (u.map K.c)ᵀ * u = 1) (a b : Fin n → K.E) :
    stdH K n (u *ᵥ a) (u *ᵥ b) = stdH K n a b := by
  have hu' : uᵀ * u.map K.c = 1 := by
    have := congrArg Matrix.transpose hu
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  have hS : ∀ y z : Fin n → K.E, stdH K n y z = y ⬝ᵥ (fun k => K.c (z k)) := fun _ _ => rfl
  have hc : (fun k => K.c ((u *ᵥ b) k)) = u.map K.c *ᵥ (fun k => K.c (b k)) := by
    funext k
    exact RingHom.map_mulVec (K.c : K.E →+* K.E) u b k
  rw [hS, hS, hc, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hu', vecMul_one]

theorem class_eq_of_conj :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' u : Matrix (Fin n) (Fin n) K.E)
      (x x' : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ →
      GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (u.map K.c)ᵀ * u = 1 → γ * u = u * γ' → B.P.Separable →
      ∃ v : B.Aˣ, (x' : B.A) = x * (v * B.σ v) := by
  intro K B n γ γ' u x x' ψ ψ' ⟨_, hg, hh⟩ ⟨_, hg', hh'⟩ hu hγ hsep
  have hgen := GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable K B hsep
  let φ : B.A →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' u ∘ₗ ψ'.toLinearMap
  have hφ_apply : ∀ y, φ y = ψ.symm (u *ᵥ ψ' y) := fun y => by
    simp [φ, Matrix.toLin'_apply]
  have hψg : ∀ w, ψ.symm (γ *ᵥ w) = B.g * ψ.symm w := fun w => by
    apply ψ.injective
    rw [hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hφg : ∀ y, φ (B.g * y) = B.g * φ y := fun y => by
    rw [hφ_apply, hφ_apply, hg', mulVec_mulVec, ← hγ, ← mulVec_mulVec, hψg]
  have hpow : ∀ (k : ℕ) y, φ (B.g ^ k * y) = B.g ^ k * φ y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ', mul_assoc, hφg, ih, ← mul_assoc]
  have hφp : ∀ (f : K.E[X]) y, φ (aeval B.g f * y) = aeval B.g f * φ y := by
    intro f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => intro y; rw [map_add, add_mul, add_mul, map_add, hp, hq]
    | monomial k e =>
      intro y
      rw [aeval_monomial, mul_assoc, ← Algebra.smul_def, map_smul, hpow, Algebra.smul_def, mul_assoc]
  have hφ : ∀ y, φ y = y * φ 1 := fun y => by
    obtain ⟨f, rfl⟩ := hgen y
    simpa using hφp f 1

  have hu2 : u * (u.map K.c)ᵀ = 1 := mul_eq_one_comm.mp hu
  have hy0 : φ (ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1)) = 1 := by
    rw [hφ_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, hu2, one_mulVec,
      LinearEquiv.symm_apply_apply]
  have hunit : IsUnit (φ 1) := by
    have h1 : ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1) * φ 1 = 1 := by rw [← hφ, hy0]
    exact ⟨⟨φ 1, ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1), by rw [mul_comm]; exact h1, h1⟩, rfl⟩
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]

  have hiso : ∀ y z, B.herm x' y z = B.herm x (y * φ 1) (z * φ 1) := fun y z => by
    rw [← hh', ← stdH_mulVec_eq_of_unitary u hu, ← hh, ← hφ, ← hφ, hφ_apply, hφ_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key : ∀ y, Algebra.trace K.E B.A (((x' : B.A) - x * (φ 1 * B.σ (φ 1))) * y) = 0 := fun y => by
    have h1 := hiso y 1
    simp only [InvAlg.herm, map_one, mul_one, one_mul] at h1
    rw [sub_mul, map_sub, h1, sub_eq_zero]
    congr 1
    ring
  exact sub_eq_zero.mp (GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hsep hgen _ key)

end GlobalTheory.InertUnitOrb
