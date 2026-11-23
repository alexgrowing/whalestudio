import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorTorusAction
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_vector_torus_action : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), VStd D i → ∀ (τ : D.what₂.Tau) (a : Fin (Wc D i).rank → ℝ) (t : T0), R.ωP i t (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * diagonal (fun j => cexp ((a j : ℂ) * I)) * (R.MW i (sg0 D A)).fr τ)) (R.ptP i t (RealDat.Delta i)) = cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • R.ptP i t (RealDat.Delta i) := by
  first | exact @GlobalTheory.AdTh.MinorWeight.delta_extremal_weight | exact GlobalTheory.AdTh.MinorWeight.delta_extremal_weight | (intros; apply GlobalTheory.AdTh.MinorWeight.delta_extremal_weight <;> assumption)
