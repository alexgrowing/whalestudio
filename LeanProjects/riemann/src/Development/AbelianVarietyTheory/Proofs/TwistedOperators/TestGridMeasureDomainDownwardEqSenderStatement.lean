import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSender
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGrid_measure_domain_downward_eq_sender : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (M : Vol G') (t : T), M.Is t → ∀ (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (e : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (H : GA D (G'.V (.grid i (j + 1))) → ℂ),
    (∀ γ ∈ GQ (G'.V (.grid i (j + 1))), ∀ g, H (γ * g) = H g) →
    (IntegrableOn (fun g => H (cast e g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ↔
      IntegrableOn H (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1)))) ∧
    ∫ g in (G.meas t i (j + 1)).fd, H (cast e g) ∂(G.meas t i (j + 1)).ν =
      ∫ g in M.fd (.grid i (j + 1)), H g ∂(M.ν (.grid i (j + 1))) := by
  first | exact @GlobalTheory.GridMeasDown.meas_down | exact GlobalTheory.GridMeasDown.meas_down | (intros; apply GlobalTheory.GridMeasDown.meas_down <;> assumption)
