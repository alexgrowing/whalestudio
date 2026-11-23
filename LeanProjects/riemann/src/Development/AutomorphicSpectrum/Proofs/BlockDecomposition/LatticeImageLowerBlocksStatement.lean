import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeImageLowerBlocks
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_image_lower_blocks : ∀ (D : D7) (n : ℕ) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n → mat k = blk4 k₁ k₂ k₃ k₄ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.CompanionTheory.MM.LowerRows.lowerRows_onto | exact GlobalTheory.CompanionTheory.MM.LowerRows.lowerRows_onto | (intros; apply GlobalTheory.CompanionTheory.MM.LowerRows.lowerRows_onto <;> assumption)
