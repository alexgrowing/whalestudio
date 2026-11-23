import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem weyl_cols {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin n) R)
    (T M : Matrix (Fin (n + n)) (Fin (n + n)) R) (hT : T.submatrix id finSumFinEquiv = Matrix.fromCols X Y)
    (h : T * blk4 0 1 (-1) 0 = M * T) : M * X = -Y ∧ M * Y = X := by
  have hJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 0 1 (-1) 0 := by
    simp [blk4]
  have h2 := congrArg (fun N : Matrix (Fin (n + n)) (Fin (n + n)) R => N.submatrix id finSumFinEquiv) h
  beta_reduce at h2
  rw [Matrix.submatrix_mul _ _ id finSumFinEquiv finSumFinEquiv finSumFinEquiv.bijective, hJ,
    Matrix.submatrix_mul _ _ id id finSumFinEquiv Function.bijective_id, Matrix.submatrix_id_id, hT,
    Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols] at h2
  obtain ⟨hX, hY⟩ := Matrix.fromCols_inj h2
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero] at hX hY
  exact ⟨hX.symm, hY.symm⟩

theorem weyl_unscale {R : Type} [CommRing R] {k l m : ℕ} (M : Matrix (Fin k) (Fin l) R) (Y : Matrix (Fin l) (Fin m) R)
    (X : Matrix (Fin k) (Fin m) R) {a b : R} (hab : b * a = 1) (h : M * (a • Y) = X) : M * Y = b • X := by
  rw [← h, Matrix.mul_smul, smul_smul, hab, one_smul]

theorem weyl_kill {R : Type} [CommRing R] {k l m : ℕ} (P : Matrix (Fin k) (Fin l) R) (X Z : Matrix (Fin l) (Fin m) R)
    {b : R} (h : P * X = 0) (hZ : Z = b • X) : P * Z = 0 := by
  rw [hZ, Matrix.mul_smul, h, smul_zero]

theorem mem_GQ_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S)
    (hX : mt S g ⬝ d.jX ∈ GlobalTheory.MixModel.ratMx D S.rank ρ) (h0 : mt S g ⬝ d.j0 ∈ GlobalTheory.MixModel.ratMx D S.rank S₀.rank)
    (hY : mt S g ⬝ d.jY ∈ GlobalTheory.MixModel.ratMx D S.rank ρ) : g ∈ GQ S := by
  rw [mem_GQ_iff, ← Matrix.mul_one (mt S g), ← d.sum_eq_one, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact add_mem (add_mem (ratMx_mul hX (rat_mem _)) (ratMx_mul h0 (rat_mem _))) (ratMx_mul hY (rat_mem _))

theorem rat_Tm_cols {D : D7} (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).submatrix id finSumFinEquiv =
      Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY) := by
  funext i j
  rcases j with j | j
  · exact congrArg (fun s => incA D (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e') i s))
      (finSumFinEquiv.symm_apply_apply (Sum.inl j))
  · exact (congrArg (fun s => incA D (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e') i s))
      (finSumFinEquiv.symm_apply_apply (Sum.inr j))).trans (map_mul (incA D) μ _)

theorem chart_weyl : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g : GA D (dblSp A), mat (κ g) = blk4 0 1 (-1) 0 → IsWeyl A g ∧ mt (dblSp A) g ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) ∧ mt (dblSp A) g ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX := by
  intro D A μ hμ κ hκ g hg
  have h := hκ g
  rw [hg] at h
  obtain ⟨e1, hY⟩ := weyl_cols _ _ _ _ (rat_Tm_cols A μ) h
  have hμ0 : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  have e2 := weyl_unscale _ _ _ hμ0 hY
  refine ⟨⟨mem_GQ_of_hypDec (dblDec A) g ?_ ?_ ?_, weyl_kill _ _ _ (dblDec A).pY_jX e2⟩, e1, e2⟩
  · exact Set.mem_of_eq_of_mem e1 (neg_mem (ratMx_smul μ (rat_mem (dblDec A).e')))
  · exact ⟨0, Matrix.ext fun _ j => Fin.elim0 j⟩
  · exact Set.mem_of_eq_of_mem e2 (ratMx_smul μ⁻¹ (rat_mem (dblDec A).e))

end GlobalTheory.StdUnn
