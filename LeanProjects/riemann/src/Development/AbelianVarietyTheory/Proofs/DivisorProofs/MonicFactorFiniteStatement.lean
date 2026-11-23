import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicFactorFinite' : MonicFactorFinite := by
  first | exact @GlobalTheory.LeviHC.monicFactorFinite | exact GlobalTheory.LeviHC.monicFactorFinite | (intros; apply GlobalTheory.LeviHC.monicFactorFinite <;> assumption)
