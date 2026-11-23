import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralSpanIffPadicWeylDualLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSpan_iff_padic_weylDualLattice : ∀ (D : D7) (Pl : Examples₂.EntPl D) (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (R : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL),
    MvPolynomial.map D.what₂.embLL R ∈ Formalism.L2.Forms.RatSpan D lam →
    (MvPolynomial.map D.what₂.embLL R ∈ Formalism.L2.Forms.IntSpan D w lam ↔
      polFun (MvPolynomial.map (Pl.iL w) R) ∈ WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau n (fun τ => (lam τ).natW)) := by
  first | exact @GlobalTheory.IntSpanCmp.intSpan_iff_delW | exact GlobalTheory.IntSpanCmp.intSpan_iff_delW | (intros; apply GlobalTheory.IntSpanCmp.intSpan_iff_delW <;> assumption)
