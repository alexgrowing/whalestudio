import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsConjOfConjNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metWeight_isConj_of_conj_norms : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y), (∀ (σ σ' : F →+* ℂ) (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → C.pn Y σ' Δ (m σ') (C.cx Y σ' (genAt Δ (under y'))) y' = C.pn Y σ Δ (m σ) (C.cx Y σ (genAt Δ (under y))) y) → ∀ σ σ', (metWeight Δ (m σ) (hm σ)).IsConj (metWeight Δ (m σ') (hm σ')) := by
  first | exact @GlobalTheory.Adopt.metWeight_isConj_of_conj_norms | exact GlobalTheory.Adopt.metWeight_isConj_of_conj_norms | (intros; apply GlobalTheory.Adopt.metWeight_isConj_of_conj_norms <;> assumption)
