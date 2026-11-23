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

namespace GlobalTheory.ChartUnip

open Matrix

theorem rat_Tm {D : D7} (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY)).submatrix id finSumFinEquiv.symm := by
  ext i j
  rcases h : finSumFinEquiv.symm j with k | k <;>
    simp [rat, Tm, HypDec.jX, HypDec.jY, Matrix.submatrix_apply, h, Matrix.map_apply]

theorem cancel_mul {R : Type*} [CommRing R] {k a m : ℕ} {P : Matrix (Fin k) (Fin (m + m)) R}
    {M : Matrix (Fin k) (Fin a) R} {N : Matrix (Fin a) (Fin m ⊕ Fin m) R}
    (h : P = M * N.submatrix id finSumFinEquiv.symm) : P.submatrix id finSumFinEquiv = M * N := by
  subst h
  ext i s
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

theorem unscale {R : Type*} [CommRing R] {k m : ℕ} {X Y Z : Matrix (Fin k) (Fin m) R} {b : Matrix (Fin m) (Fin m) R}
    {u v : R} (huv : u * v = 1) (h : X * b + v • Y = v • Z) : Z = Y + X * (u • b) := by
  have h3 := congrArg (fun M => u • M) h
  simp only [smul_add, smul_smul, huv, one_smul] at h3
  rw [Matrix.mul_smul, add_comm, h3]

theorem skew_of_image {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S) (c : Mx D ρ ρ)
    (hY : mt S g ⬝ d.jY = d.jY + d.jX ⬝ c) : c ∈ skewA D ρ := by
  have h0 : adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ (mt S g ⬝ d.jY)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ (mt_unitary S g), d.gram_YY]
  rw [hY] at h0
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY,
    d.gram_XY, cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at h0
  exact mem_skewA.2 (eq_neg_of_add_eq_zero_left h0)

theorem chart_unip : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (g : GA D (dblSp A)) (b : Mx D A.rank A.rank), mat (κ g) = blk4 1 b 0 1 →
    ∃ c : skewA D A.rank, c.1 = incA D μ⁻¹ • b ∧ g = (dblDec A).nC c := by
  intro D A μ hμ κ hκ g b hg
  have hT := hκ g
  rw [hg, rat_Tm, blk4, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks] at hT
  have hT' := cancel_mul hT
  rw [mul_fromCols, Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self, Matrix.submatrix_id_id] at hT'
  obtain ⟨h1, h2⟩ := fromCols_inj hT'
  rw [Matrix.mul_one, Matrix.mul_zero, add_zero] at h1
  rw [Matrix.mul_one, Matrix.mul_smul] at h2
  have hunit : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  have hX : mt (dblSp A) g ⬝ (dblDec A).jX = (dblDec A).jX := h1.symm
  have hY : mt (dblSp A) g ⬝ (dblDec A).jY = (dblDec A).jY + (dblDec A).jX ⬝ (incA D μ⁻¹ • b) :=
    unscale hunit h2
  refine ⟨⟨incA D μ⁻¹ • b, skew_of_image (dblDec A) g _ hY⟩, rfl, ?_⟩
  refine (dblDec A).ga_ext ?_ (Matrix.ext fun _ j => Fin.elim0 j) ?_
  · rw [hX, HypDec.nC_jX]
  · rw [hY, HypDec.nC_jY]

end GlobalTheory.ChartUnip
