import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomNormSqEqInfiniteSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_norm_sq_eq_infinite_sq : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (x : ToroidalCompactificationData s) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw), ∀ g ∈ cuspOn (unf s) Z (wtOf S.Dw la 0), ∀ σ : κ.c.F →+* ℂ, GoodEmb κ.c σ → ∀ z ∈ framesOn (unf s σ) Z, ∃ (σ' : D.what₂.LL →+* ℂ) (y : Pts (Φ.C k).Y σ'), y ∈ offBd Φ k σ' ∧ homN (unf s σ) (xiR D) (wtOf S.Dw la 0) g z ^ 2 = infSq Φ k x la σ' ((Φ.C k).val g) y := by
  first | exact @GlobalTheory.CovHt.Link.homN_sq_eq_infSq | exact GlobalTheory.CovHt.Link.homN_sq_eq_infSq | (intros; apply GlobalTheory.CovHt.Link.homN_sq_eq_infSq <;> assumption)
