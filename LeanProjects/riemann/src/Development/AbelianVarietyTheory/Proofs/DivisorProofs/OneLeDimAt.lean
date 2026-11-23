import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.DimAtOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_dimAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := by
  intro D i τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt
  have h := Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ (GlobalTheory.AdelicScalar.sig_add i τ)
  have h1 : (1 : ℚ) ≤ dimK _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) τ) :=
    one_le_mul_of_one_le_of_one_le (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.1) (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.2.1)
  exact_mod_cast h1

end GlobalTheory.DimAtOne
