import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRangeStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.ChartSymm

theorem continuous_mat {D : D7} {n : ℕ} : Continuous (mat : G D n → Mx D (n + n) (n + n)) := by
  unfold GlobalTheory.StdUnn.mat
  exact Continuous.comp' Units.continuous_val continuous_induced_dom

private theorem gram_conjTranspose_eq_self {D : D7} (S : HSp D) :
    (Formalism.BasicNotions.HSpace.gram S).conjTranspose = Formalism.BasicNotions.HSpace.gram S := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.BasicNotions.HSpace.gram]
  exact S.herm.eq (S.frame j) (S.frame i)

private theorem fromRows_gram_mul_fromCols_eq_one_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E)
    (hμ : μ ≠ 0) :
    Matrix.fromRows (d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S)
        (μ⁻¹ • (d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S)) *
      Matrix.fromCols d.e (μ • d.e') = 1 := by
  have h1 : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 1 := d.e'e
  have h0 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 0 := d.ee
  have h0' : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 0 := d.e'e'
  have h2 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose h1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose_eq_self,
      Matrix.conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  rw [Matrix.fromRows_mul_fromCols]
  simp only [Matrix.mul_smul, Matrix.smul_mul, h1, h0, h0', h2, smul_zero, smul_smul,
    inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ, one_smul, Matrix.fromBlocks_one]

theorem continuous_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ (κ : GA D (dblSp A) ≃* G D A.rank), IsChart A μ κ →
    Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hL : ((Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id) * Tm A μ = 1 := by
    show _ * (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, fromRows_gram_mul_fromCols_eq_one_of_hypDec _ μ hμ.1,
      Matrix.submatrix_one_equiv]
  have hR := mul_eq_one_comm.mp hL
  set L := (Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id with hLdef
  have hTP : rat (Tm A μ) * rat L = (1 : Mx D (A.rank + A.rank) (A.rank + A.rank)) := by
    show (incA D).mapMatrix (Tm A μ) * (incA D).mapMatrix L = 1
    rw [← map_mul, hR, map_one]
  have key : ∀ h : G D A.rank, mt (dblSp A) (κ.symm h) = rat (Tm A μ) * mat h * rat L := by
    intro h
    have e := hκ (κ.symm h)
    rw [MulEquiv.apply_symm_apply] at e
    calc mt (dblSp A) (κ.symm h) = mt (dblSp A) (κ.symm h) * (rat (Tm A μ) * rat L) := by
          rw [hTP, Matrix.mul_one]
      _ = (mt (dblSp A) (κ.symm h) * rat (Tm A μ)) * rat L := by rw [Matrix.mul_assoc]
      _ = rat (Tm A μ) * mat h * rat L := by rw [← e]
  have hind : Topology.IsInducing (fun g : GA D (dblSp A) => matHom (dblSp A) g) := ⟨rfl⟩
  have hmi : Continuous (fun h : G D A.rank => mat h⁻¹) := by
    unfold GlobalTheory.StdUnn.mat
    simp only [map_inv]
    exact Units.continuous_coe_inv.comp continuous_induced_dom
  rw [hind.continuous_iff, Units.continuous_iff]
  constructor
  · have hf : (Units.val ∘ (fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) =
        fun h => rat (Tm A μ) * mat h * rat L := by
      funext h
      exact key h
    rw [hf]
    exact (continuous_const.matrix_mul continuous_mat).matrix_mul continuous_const
  · have hf : (fun h : G D A.rank => (((fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) h)⁻¹.val) =
        fun h => rat (Tm A μ) * mat h⁻¹ * rat L := by
      funext h
      simp only [Function.comp_apply]
      rw [← map_inv (matHom (dblSp A)), ← map_inv κ.symm]
      exact key h⁻¹
    rw [hf]
    exact (continuous_const.matrix_mul hmi).matrix_mul continuous_const

end GlobalTheory.CompanionTheory.ChartSymm
