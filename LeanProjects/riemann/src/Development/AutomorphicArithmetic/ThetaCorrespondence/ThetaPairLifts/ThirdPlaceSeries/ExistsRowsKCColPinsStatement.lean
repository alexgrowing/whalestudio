import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqDataStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPins

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_integrable_columns_of_heq_data : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex), KPin q t → Nonempty (RXs q.x.what₂) → ∃ Dc Sp₀ Zsc₀, ∃ C₀ : ReadC q.x.what₂.r.z.R (reFace q.x.what₂.r.z.F Dc Sp₀ Zsc₀) q.O.ex.p0 ((q.x.what₂.r.Y)), ∀ (T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex), T.ker = t → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → a.Dc = Dc → HEq x.C.wU C₀.wU → HEq x.C.eNu C₀.eNu → ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS := by
  first | exact @_root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses | exact _root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses | (intros; apply _root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses <;> assumption)
end
