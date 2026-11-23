import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.CompanionTheory.SwUnf

def lowerC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

variable {D : D7} {n : ℕ}

def cellKer (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin n → D.host.E) :=
  LinearMap.ker (lowerC x).mulVecLin

def ratOf (γ : GF D n) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E :=
  Classical.choose (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

theorem mat_ratOf (γ : GF D n) : mat (γ : G D n) = (ratOf γ).map (incA D) :=
  Classical.choose_spec (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

def cosetCell (q : GlobalTheory.Eis.Cosets (P D n) (GF D n)) : Submodule D.host.E (Fin n → D.host.E) :=
  cellKer (ratOf (q.out))

end GlobalTheory.CompanionTheory.SwUnf
