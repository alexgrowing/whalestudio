import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem le_of_mul_pow_eq_pow {m n : ℕ} {y : F} (hy : y ∈ 𝒪[F])
    (h : y * (GLnLocal.uniformizer F : F) ^ n = (GLnLocal.uniformizer F : F) ^ m) : n ≤ m := by
  have hb := (bdd_of_mem hy).mul (bdd_zpow (F := F) (n : ℤ))
  rw [zero_add, zpow_natCast, h, ← zpow_natCast] at hb
  exact_mod_cast le_of_bdd_zpow hb

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem entries_of_mul_eq {K : Matrix (Fin 2) (Fin 2) F} {x y z x' y' z' : F}
    (h : K * !![x', y'; 0, z'] = !![x, y; 0, z]) :
    K 0 0 * x' = x ∧ K 1 0 * x' = 0 ∧ K 0 0 * y' + K 0 1 * z' = y ∧
      K 1 0 * y' + K 1 1 * z' = z := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h10 h01 h11
  refine ⟨h00, ?_, h01, h11⟩
  simpa using h10

theorem rowRep_unique (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (a b : Σ _ : ℕ, Σ j : ℕ, (Fin j → 𝓀[F]))
    (h : rowRep a.1 a.2.1 a.2.2 * (rowRep b.1 b.2.1 b.2.2)⁻¹ ∈ integralGL F 2) : a = b := by
  obtain ⟨i, j, c⟩ := a
  obtain ⟨i', j', c'⟩ := b
  dsimp only at h
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  obtain ⟨hO, hI⟩ := (mem_integralGL_iff F 2).1 h
  set κ := rowRep i j c * (rowRep i' j' c')⁻¹ with hκ
  have e1 : (κ : Matrix (Fin 2) (Fin 2) F) * (rowRep i' j' c' : Matrix (Fin 2) (Fin 2) F) =
      (rowRep i j c : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, hκ, inv_mul_cancel_right]
  have e2 : ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (rowRep i j c : Matrix (Fin 2) (Fin 2) F) =
      (rowRep i' j' c' : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, hκ, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
  rw [coe_rowRep, coe_rowRep] at e1 e2
  obtain ⟨p1, r1, q1, s1⟩ := entries_of_mul_eq e1
  obtain ⟨p2, r2, q2, s2⟩ := entries_of_mul_eq e2
  have hr : (κ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    (mul_eq_zero.1 r1).resolve_right (pow_ne_zero _ hϖ)
  have hr' : ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    (mul_eq_zero.1 r2).resolve_right (pow_ne_zero _ hϖ)
  rw [hr, zero_mul, zero_add] at s1
  rw [hr', zero_mul, zero_add] at s2
  have hi : i = i' := le_antisymm (le_of_mul_pow_eq_pow (hI 0 0) p2) (le_of_mul_pow_eq_pow (hO 0 0) p1)
  have hj : j = j' := le_antisymm (le_of_mul_pow_eq_pow (hI 1 1) s2) (le_of_mul_pow_eq_pow (hO 1 1) s1)
  subst hi hj
  have hp : (κ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    mul_right_cancel₀ (pow_ne_zero i hϖ) (by rw [p1, one_mul])
  rw [hp, one_mul] at q1
  have hb : Bdd F (j : ℤ) (digitSum F j c - digitSum F j c') := by
    have := (bdd_of_mem (hO 0 1)).mul (bdd_zpow (F := F) (j : ℤ))
    rw [zero_add, zpow_natCast] at this
    convert this using 1
    rw [← q1]
    ring
  rw [eq_of_bdd_digitSum_sub j hb]

end GlobalTheory.CompanionTheory.LFUDom
