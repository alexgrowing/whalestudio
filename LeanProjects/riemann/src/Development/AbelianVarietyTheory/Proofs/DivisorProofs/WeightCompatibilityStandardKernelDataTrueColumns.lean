import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightTieTrueCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGapStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)

noncomputable section

namespace GlobalTheory.ColRows

set_option maxHeartbeats 1000000 in

theorem weightTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
  obtain ⟨hX, -, hPr, -, -, -, hword, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  subst hX
  cases hPr
  cases hword
  cases hW
  have hN := GlobalTheory.T.columnNormParameters_eq_natStepGap (I.rec7 l Z) L Del h0 hDel hEta
  refine ⟨plRec (I.rec7 l Z), fun u => ?_⟩
  have key := GlobalTheory.CoreHt.weightTie_trueCols I hOk l Z L ⟨Del, hDel⟩ u
  have gen : ∀ N : NumDatum, numDatumOfParameters (I.rec7 l Z) L = N → ∀ (W' : Wts B.fields (B.primes X).Word N.R), HEq B.wts W' →
      ∀ (pl' : RPl N.R ≃ B.fields.Tau), HEq (plRec (I.rec7 l Z)) pl' → ∀ δ : Code N, HEq (codeRec L u) δ →
      GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie N (X := B.fields) (Pr := B.primes X) W' pl' u δ := by
    intro N hN W' hW' pl' hpl δ hδ
    subst hN
    cases hW'
    cases hpl
    cases hδ
    exact key
  exact gen _ hN _ HEq.rfl _ HEq.rfl _ HEq.rfl

end GlobalTheory.ColRows

end
