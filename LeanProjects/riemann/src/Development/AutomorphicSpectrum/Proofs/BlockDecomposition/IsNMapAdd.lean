import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem isNMap_add : ∀ {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) (x y : hermA D p), nb (x + y) = nb x * nb y := by
  intro D p nb hnb x y
  apply mat_inj
  rw [mat_mul, hnb, hnb, hnb, submatrix_fromBlocks_mul]
  simp [add_comm]

end GlobalTheory.CompanionTheory.MuC
