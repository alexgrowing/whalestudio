import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

def pull (a : GL (Fin n) (AE D)) (b : hermA D n) : hermA D n :=
  ⟨(a⁻¹).1 * b.1 * adj (a⁻¹).1, by
    have hb : adj b.1 = b.1 := b.2
    change adj _ = _
    rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]⟩

theorem adj_one' : adj (1 : Mx D n n) = 1 := by
  show ((1 : Mx D n n).map (cA D))ᵀ = 1
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

def astar (a : GL (Fin n) (AE D)) : GL (Fin n) (AE D) :=
  ⟨adj (a⁻¹).1, adj a.1,
    by
      rw [← adj_mul]
      have : a.1 * (a⁻¹).1 = 1 := by simp
      rw [this, adj_one'],
    by
      rw [← adj_mul]
      have : (a⁻¹).1 * a.1 = 1 := by simp
      rw [this, adj_one']⟩

def gAt (θ : InfFam D) (a : GL (Fin n) (AE D)) (τ : D.what₂.Tau) : GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.map ((θ τ).comp (infPart D)) a

def latAt (h : Matrix (Fin n) (Fin n) (AE D))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) :
    AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup.map
    (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v h)).toAddMonoidHom

end GlobalTheory.CompanionTheory.MM
