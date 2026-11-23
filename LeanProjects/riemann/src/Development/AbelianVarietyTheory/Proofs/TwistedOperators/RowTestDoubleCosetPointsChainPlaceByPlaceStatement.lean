import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDoubleCosetPointsChainPlaceByPlace
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
theorem _root_.GlobalTheory.T.rowTest_doubleCosetPoints_chain_place_by_place : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ p : Pts ch.G, IsRealPt p → ∃ q : Finset (locPl ch.G t) → Pts ch.G, q ∅ = p * b₀ ∧ q Finset.univ = p * b ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∃ r r₀ h : Pts ch.G, OneLoc t w.1 (eL w) r (fun j => if j ∈ idx D then sgnAt ch.G t s w.1 j * (repsAt ch.G t w.1).elt (β w) (D.R.m, j) else 1) ∧ OneLoc t w.1 (eL w) r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) j)⁻¹ else 1) ∧ (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.1.under (𝓞 D.host.F))) ∧ h * r = q (insert w S) ∧ h * r₀ = q S := by
  first | exact @GlobalTheory.PlaceChain.points | exact GlobalTheory.PlaceChain.points | (intros; apply GlobalTheory.PlaceChain.points <;> assumption)
