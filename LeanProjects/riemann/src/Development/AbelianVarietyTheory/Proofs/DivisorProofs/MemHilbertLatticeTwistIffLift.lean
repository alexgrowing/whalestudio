import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistMem

variable {F : Type} [Field F] [NumberField F]

theorem vecMul_mem_std (B : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hy 0 (Set.mem_univ _)
  have h1 := hy 1 (Set.mem_univ _)
  have : Matrix.vecMul y (B.map (Int.cast : ℤ → F)) j = B 0 j • y 0 + B 1 j • y 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ h0) (Submodule.smul_of_tower_mem _ _ h1)

theorem exists_lift_diff (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
      ((A.map (Int.cast : ℤ → ZMod N)).map (ZMod.cast : ZMod N → ℤ)).map (Int.cast : ℤ → F)
        = A.map (Int.cast : ℤ → F) + (N : F) • B.map (Int.cast : ℤ → F) := by
  have h : ∀ a : ℤ, ∃ b : ℤ, (ZMod.cast (a : ZMod N) : ℤ) = a + N * b := by
    intro a
    have h1 : ((a : ℤ) : ZMod N) = (((ZMod.cast (a : ZMod N) : ℤ) : ℤ) : ZMod N) := by
      simp
    obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).1 h1
    exact ⟨b, by linarith⟩
  choose f hf using h
  refine ⟨A.map f, ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hf]
  push_cast
  ring

theorem vecMul_scalar (N : ℕ) (w : Fin 2 → F) :
    Matrix.vecMul w ((((N : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ))).map (Int.cast : ℤ → F)) = (N : F) • w := by
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Matrix.natCast_apply, mul_comm]

theorem mem_twist_iff (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F) (hL : L ≤ stdLat F) :
    (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔
      ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by
  obtain ⟨B, hB⟩ := exists_lift_diff (F := F) N A
  unfold twist mulMat
  simp only [Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply,
    Matrix.vecMulLinear_apply, hB, vecMul_scalar, Matrix.vecMul_add, Matrix.vecMul_smul]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨y, hy, Matrix.vecMul y (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (vecMul_mem_std B (hL hy)) hw, ?_⟩
    rw [smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨_, ⟨y, hy, rfl⟩, _, ⟨w - Matrix.vecMul y (B.map (Int.cast : ℤ → F)),
      Submodule.sub_mem _ hw (vecMul_mem_std B (hL hy)), rfl⟩, ?_⟩
    rw [smul_sub]
    abel

end GlobalTheory.HilbFam.TwistMem
