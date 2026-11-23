import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsPrimeWeightSizesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizeInequalitiesNoLevelPrimeColumnNormParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGapStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows

set_option maxHeartbeats 800000 in

theorem kerSizes_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → (∀ u, Real.log ((((I.rec7 l Z).mem u).A.T : ℕ) : ℝ) ≤ CT * (I.rec7 l Z).R.m * L.sc.L) → GlobalTheory.ColRows.KerSizes t W Del h0 CY CT := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta CY CT hH hX' hx hTa hlogT
  have hNum := GlobalTheory.T.columnNormParameters_eq_natStepGap (I.rec7 l Z) L Del h0 hDel hEta
  have hSz := GlobalTheory.T.trueColumns_prime_weight_sizes I hOk l Z L CY hH hX' hx hTa
  refine ⟨?_, ?_, hlogT⟩
  · obtain ⟨hX, -, hPr, -⟩ := hS
    cases t
    dsimp only at hX hPr W hW ⊢
    subst hX
    cases eq_of_heq hPr
    cases eq_of_heq hW
    exact hSz
  · intro u
    have h := GlobalTheory.T.sizeInequalitiesNoLevelPrime_columnNormParameters (I.rec7 l Z) L CY hH u
    unfold GlobalTheory.ColumnNormCompare.codeRec at h
    convert h using 1 <;> first | exact hNum.symm | exact HEq.rfl | rfl

end GlobalTheory.ColRows
