import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped Matrix

namespace GlobalTheory.RealColAct

variable {D : D7}

theorem gramAt_of_gram_one {V : HSp D} (hV : HSpace.gram V = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [hV]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_mem_unitary {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : HSpace.gram V = 1) (g : GA D V)
    (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  have h := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  rw [gramAt_of_gram_one hV, Matrix.mul_one] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact h

theorem transpose_mem_unitary {n : ℕ} {K : Matrix (Fin n) (Fin n) ℂ} (hK : K ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Kᵀ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h2 : K * star K = 1 := Matrix.mem_unitaryGroup_iff.1 hK
  rw [Matrix.mem_unitaryGroup_iff']
  have e : star Kᵀ = (star K)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]; rfl
  rw [e, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

def realCol (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    GinfC V →* (D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ) where
  toFun g τ := ⟨(compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ,
    transpose_mem_unitary (compAt_mem_unitary hθ hV _ τ)⟩
  map_one' := by
    funext τ
    apply Subtype.ext
    simp only [OneMemClass.coe_one, inv_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.transpose_one, Pi.one_apply]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.transpose_mul, Pi.mul_apply]
    rfl

theorem realCol_apply (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) (g : GinfC V) (τ : D.what₂.Tau) :
    (realCol θ hθ V hV g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ := rfl

end GlobalTheory.RealColAct
