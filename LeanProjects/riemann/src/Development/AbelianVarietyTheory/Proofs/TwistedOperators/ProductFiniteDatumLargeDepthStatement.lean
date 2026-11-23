import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFiniteDatum_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m) (d₁ d₂ : FinDatum ch.G t (.top t j)) (c₁ c₂ : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), IsIdemSum (d₁.e + d₂.e) (d₁.P ∪ d₂.P) → IsCombOf ch.W d₁ c₁ → IsCombOf ch.W d₂ c₂ → ∃ (d : FinDatum ch.G t (.top t j)) (c : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), d.P = d₁.P ∪ d₂.P ∧ d.e = d₁.e + d₂.e ∧ IsCombOf ch.W d c ∧ (∀ y, IsHalf d.e y → d.fn y = d₁.fn (d₁.e • y) * d₂.fn (d₂.e • y)) ∧ ∀ f, comb ch.W.ψ _ _ c f = comb ch.W.ψ _ _ c₁ (comb ch.W.ψ _ _ c₂ f) := by
  first | exact @GlobalTheory.ProdDatum.prod_datum | exact GlobalTheory.ProdDatum.prod_datum | (intros; apply GlobalTheory.ProdDatum.prod_datum <;> assumption)
