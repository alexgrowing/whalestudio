import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalCuspType
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_horizontal_cusp_type : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε := by
  first | exact @GlobalTheory.CuspFormApprox.th_formApprox | exact GlobalTheory.CuspFormApprox.th_formApprox | (intros; apply GlobalTheory.CuspFormApprox.th_formApprox <;> assumption)
