import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRestrict

theorem hE_col0v_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n r : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (A B : Matrix (Fin n) (Fin (r + 1)) E) :
    hE σ J (GlobalTheory.EisMidHt.firstColumn A) (GlobalTheory.EisMidHt.firstColumn B) = (Formalism.UG.cT (σ : E →+* E) A * J * B) 0 0 := by
  simp only [hE, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    GlobalTheory.EisMidHt.firstColumn, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dim_add_two (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    dim σ J X Y + 2 = n := by
  set x₀ := GlobalTheory.EisMidHt.firstColumn X
  set y₀ := GlobalTheory.EisMidHt.firstColumn Y
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx hσ hJ hW
  have hxy : hE σ J x₀ y₀ = 1 := by rw [hE_col0v_entry, hW.xy]; simp
  have hyx' : hE σ J y₀ x₀ = 1 := by rw [hE_col0v_entry, hyx]; simp
  have hxx : hE σ J x₀ x₀ = 0 := by rw [hE_col0v_entry, hW.xx]; simp
  have hyy : hE σ J y₀ y₀ = 0 := by rw [hE_col0v_entry, hW.yy]; simp
  let φ := (hRight σ J x₀).prod (hRight σ J y₀)
  have hker : LinearMap.ker φ = V0 σ J X Y := by
    rw [LinearMap.ker_prod]; rfl
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨a • y₀ + b • x₀, ?_⟩
    simp only [φ, LinearMap.prod_apply, Pi.prod, map_add, map_smul, Prod.mk.injEq]
    simp only [hRight, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, Function.prod, Prod.smul_mk, Prod.mk_add_mk]
    rw [hxy, hyx', hxx, hyy]; simp
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, hker, finrank_top, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at h
  simp only [dim]
  omega

end GlobalTheory.EisRestrict
