import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeil
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem absA_pos (z : (AE D)ˣ) : 0 < absA D z := by
  have h : absA D z * absA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h

theorem npow_neg_nat {r : ℝ≥0} (hr : 0 < r) (m : ℕ) : ((((r ^ m)⁻¹ : ℝ≥0) : ℝ) : ℂ) = npow r (-(m : ℂ)) := by
  have h0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem integral_comp_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (f : A → ℂ) :
    ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ := by
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ y, f (φ y) ∂μ :=
    integral_map_equiv (μ := μ) φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (x y : hermA D n) : nb (x + y) = nb x * nb y :=
  mat_inj (by
    rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
    simp [add_comm])

def cg (a : GL (Fin n) (AE D)) (c : hermA D n) : hermA D n :=
  ⟨a.1 * c.1 * adj a.1, by
    change adj (a.1 * c.1 * adj a.1) = a.1 * c.1 * adj a.1
    have hc : adj c.1 = c.1 := c.2
    rw [adj_mul, adj_mul, adj_adj, hc, Matrix.mul_assoc]⟩

theorem adj_mul_adj_inv (a : GL (Fin n) (AE D)) : (adj a.1 : Mx D n n) * adj (a⁻¹).1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

theorem adj_inv_mul_adj (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

def ad (a : GL (Fin n) (AE D)) : GL (Fin n) (AE D) :=
  ⟨adj (a⁻¹).1, adj a.1, adj_inv_mul_adj a, adj_mul_adj_inv a⟩

theorem nb_cg_mul {nb : hermA D n → G D n} (h : IsNMap nb) (a : GL (Fin n) (AE D)) {m : G D n}
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (c : hermA D n) : nb (cg a c) * m = m * nb c :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, h, h, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    have e : a.1 * c.1 * adj a.1 * adj (a⁻¹).1 = a.1 * c.1 := by
      rw [Matrix.mul_assoc, adj_mul_adj_inv, Matrix.mul_one]
    simp [cg, e, -Matrix.coe_units_inv])

theorem weyl_mul {w m m' : G D n} (hw : mat w = blk4 0 1 (-1) 0) (a : GL (Fin n) (AE D))
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (hm' : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1) : w * m = m' * w :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, hw, hm', submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp)

theorem mulVec_mem_upper {g : G D n} {x y : Mx D n n} (hg : mat g = blk4 x 0 0 y) {v : Fin (n + n) → AE D}
    (hv : v ∈ upperHalf D n) : (mat g).mulVec v ∈ upperHalf D n := by
  have hv' : ∀ i : Fin n, v (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := fun i => congrFun hv i
  refine LinearMap.mem_ker.2 (funext fun i => ?_)
  simp only [LinearMap.funLeft_apply, Pi.zero_apply, hg, Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    hv', mul_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem levi_mem_P {g g' : G D n} {x y x' y' : Mx D n n} (hg : mat g = blk4 x 0 0 y) (hg' : mat g' = blk4 x' 0 0 y')
    (h1 : g' * g = 1) : g ∈ P D n := by
  have hinv : g⁻¹ = g' := inv_eq_of_mul_eq_one_left h1
  intro v
  refine ⟨fun hv => mulVec_mem_upper hg hv, fun hv => ?_⟩
  have h2 := mulVec_mem_upper hg' (v := (mat g).mulVec v) hv
  rwa [Matrix.mulVec_mulVec, ← mat_mul, h1, mat_one, Matrix.one_mulVec] at h2

theorem height_mul {H : G D n → ℝ≥0} (hH : IsHeight H) {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D))
    (ha : blkA (mat p) = a.1) (x : G D n) :
    H (p * x) = absA D (Matrix.GeneralLinearGroup.det a) * H x := by
  obtain ⟨q, hq, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨c, hc⟩ := exists_blkA hq
  have e : blkA (mat (p * q)) = (a * c).1 := by rw [blkA_mul hq, ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hq) (a * c) e k hk, hH q hq c hc k hk, map_mul, map_mul]

end GlobalTheory.CompanionTheory.IwaAd
