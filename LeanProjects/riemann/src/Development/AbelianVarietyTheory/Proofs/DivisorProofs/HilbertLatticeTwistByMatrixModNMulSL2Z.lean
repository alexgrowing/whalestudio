import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLiftStatement

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistSL

theorem vecMul_mem_stdLat {F : Type} [Field F] [NumberField F] (B : Matrix (Fin 2) (Fin 2) ℤ) {w : Fin 2 → F}
    (hw : w ∈ stdLat F) : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hw 0 (Set.mem_univ _)
  have h1 := hw 1 (Set.mem_univ _)
  have e : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j = B 0 j • w 0 + B 1 j • w 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  change Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (zsmul_mem h0 _) (zsmul_mem h1 _)

theorem map_cast_mul (R : Type) [CommRing R] (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map (Int.cast : ℤ → R) = A.map (Int.cast : ℤ → R) * B.map (Int.cast : ℤ → R) :=
  Matrix.map_mul (f := Int.castRingHom R)

theorem twist_mul_sl : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro F _ _ _ N L α γ hL
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, α = A.map (Int.cast : ℤ → ZMod N) :=
    ⟨α.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  rw [← map_cast_mul]
  have hinv : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) *
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) = 1 := by
    rw [← map_cast_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.map_one _ Int.cast_zero Int.cast_one
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L _ v hL]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)) +
      (N : F) • Matrix.vecMul w (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)), ?_, ?_⟩
    · exact (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, _, vecMul_mem_stdLat _ hw, rfl⟩
    · rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hinv,
        Matrix.vecMul_one, map_cast_mul]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).1 hu
    refine ⟨y, hy, _, vecMul_mem_stdLat (γ : Matrix (Fin 2) (Fin 2) ℤ) hw, ?_⟩
    rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, map_cast_mul]

end GlobalTheory.HilbFam.TwistSL
