import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightDecompositionClosedPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_decomposition_closed_point : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (M : Adl C Y) (ι : Type) [Fintype ι] (ρ : ι → Adl C Y) (t : ι → ℝ) (g : ∀ σ, Pts Y σ → ℝ), IsComb M ρ t g → (∀ i (y : AlgPt Y), {v : HeightOneSpectrum (𝓞 F) | ∃ e : TrueGeo.Ext v, (ρ i).lg v e y ≠ 0}.Finite) → ∀ x : Y.X, IsClosed ({x} : Set Y.X) → M.ht x = ∑ i, t i * (ρ i).ht x + (∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), g σ z) / ((Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ)) := by
  first | exact @GlobalTheory.Mean4O.HtComb.main | exact GlobalTheory.Mean4O.HtComb.main | (intros; apply GlobalTheory.Mean4O.HtComb.main <;> assumption)
