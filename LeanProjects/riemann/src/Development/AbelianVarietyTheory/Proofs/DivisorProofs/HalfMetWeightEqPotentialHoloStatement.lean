import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfMetWeightEqPotentialHolo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_metWeight_eq_potential_holo : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (D : ℕ) (A : FinHolAtlas D (Pts Y σ)), IsAlgAtlas A → ∀ (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (Q : LocPot (Pts Y σ)), IsPot id m Q → ∀ (x : Pts Y σ) (c : (toLB Δ).ι), x ∈ ptsIn Y.str σ ((toLB Δ).U c) → ∃ W : Set (Pts Y σ), IsOpen W ∧ x ∈ W ∧ ∃ G : Pts Y σ → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, (metWeight Δ m hm).φ c z / 2 = Q.φ x z + (G z).re := by
  first | exact @GlobalTheory.Adopt.half_metWeight_eq_potential_holo | exact GlobalTheory.Adopt.half_metWeight_eq_potential_holo | (intros; apply GlobalTheory.Adopt.half_metWeight_eq_potential_holo <;> assumption)
