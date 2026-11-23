import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ColStd

theorem sum_smul_col {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) (c : Fin n → 𝓞 K) :
    (∑ j, c j • (fun a => (B : Matrix (Fin n) (Fin n) K) a j)) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => algebraMap (𝓞 K) K (c j)) := by
  ext a
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mulVec_inj {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) {x y : Fin n → K}
    (h : (B : Matrix (Fin n) (Fin n) K) *ᵥ x = (B : Matrix (Fin n) (Fin n) K) *ᵥ y) : x = y := by
  have key : ∀ z : Fin n → K, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((B : Matrix (Fin n) (Fin n) K) *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← key x, h, key y]

theorem colLat_comap_eq_stdLat {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) :
    (Formalism.L2.DIV.colLat B).comap ((Matrix.mulVecLin B.1).restrictScalars (𝓞 K)) = Formalism.L2.Pj.stdLat K n := by
  ext v
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    Formalism.L2.DIV.colLat]
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hv
    rw [sum_smul_col] at hc
    have := mulVec_inj B hc
    intro i
    exact ⟨c i, congrFun this i⟩
  · intro hv
    choose w hw using hv
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).2 ⟨w, ?_⟩
    rw [sum_smul_col]
    congr 1
    funext j
    exact hw j

end GlobalTheory.ColStd
