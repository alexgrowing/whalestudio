import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ValueFormula
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChart

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

variable {D : D7}

theorem blk4_map_alt {n : ℕ} (f : D.host.E →+* AE D) (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem adj_map_herm {n : ℕ} (b : HermQ D n) : adj (b.1.map (incA D) : Mx D n n) = b.1.map (incA D) := by
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← b.2 i j]
  rfl

theorem cell_value {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) {b : Mx D n n} (hu : mat u = blk4 1 b 0 1) (Φ : schwartzA θ V.rank n) :
    (ω (w * u) Φ).1 0 = ∫ y, Φ.1 y * ψ (halfTr (Matrix.trace (HMul.hMul b (StdUnn.inner V y y) : Mx D n n))) ∂μ := by
  rw [map_mul, Module.End.mul_apply, hω.weyl w hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have z : StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  simp only [z, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hω.unip u b hu, mul_comm]

theorem mat_cell {n : ℕ} {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) {b : Mx D n n} (hu : mat u = blk4 1 b 0 1) :
    mat (w * u) = blk4 0 1 (-1) (-b) := by
  rw [mat_mul, hw, hu, submatrix_fromBlocks_mul]
  simp

theorem cell_mem_GF {n : ℕ} {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : HermQ D n)
    (hu : mat u = blk4 1 (b.1.map (incA D)) 0 1) : w * u ∈ GF D n := by
  rw [ChartRat.mem_GF_iff, mat_cell hw hu]
  refine ⟨blk4 0 1 (-1) (-b.1), ?_⟩
  change (blk4 0 1 (-1) (-b.1)).map (incA D) = _
  rw [blk4_map_alt]
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  have e2 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = -1 := by
    have := map_neg (incA D).mapMatrix (1 : Matrix (Fin n) (Fin n) D.host.E)
    rwa [map_one] at this
  have e3 : (-b.1).map (incA D) = -(b.1.map (incA D)) := map_neg (incA D).mapMatrix b.1
  rw [e0, e1, e2, e3]

theorem cell_inj {n : ℕ} {w u u' : G D n} (hw : mat w = blk4 0 1 (-1) 0) {b b' : Mx D n n} (hu : mat u = blk4 1 b 0 1)
    (hu' : mat u' = blk4 1 b' 0 1) (h : (w * u') * (w * u)⁻¹ ∈ P D n) : b = b' := by
  obtain ⟨β, d, hp⟩ := siegelParabolicUnn_matrix_blockUpperTriangular h
  have e : mat ((w * u') * (w * u)⁻¹) * mat (w * u) = mat (w * u') := by
    rw [← mat_mul, inv_mul_cancel_right]
  rw [hp, mat_cell hw hu, mat_cell hw hu', submatrix_fromBlocks_mul] at e
  obtain ⟨-, -, h3, h4⟩ := blockMatrixTwoByTwoFin_injective e
  simp only [mul_zero, mul_neg, mul_one, zero_mul, add_zero, zero_add, neg_inj] at h3 h4
  rw [h3] at h4
  simpa using h4

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
