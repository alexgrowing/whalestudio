import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueChainsKernelDatumSourceSideLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelDatumLatticeTargetSideTrueChainsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChainsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntHyp_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → KerEntHyp Pl O Bs Y (I.tw l l0 Z) := fun I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8 =>
  ⟨GlobalTheory.T.targetPairing_sizes_in_coefficientField_valueGroup I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.trueChains_kernelDatum_sourceSideLattice I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.kernelDatum_lattice_target_side_trueChains I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.kernelEntries_form_true_chains I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8⟩

end GlobalTheory.Mem.Col2.TC

end
