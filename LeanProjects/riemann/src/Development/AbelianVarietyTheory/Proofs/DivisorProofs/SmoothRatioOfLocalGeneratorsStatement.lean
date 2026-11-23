import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRatioOfLocalGenerators
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_ratio_of_local_generators : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (C : Closeds Y.X) (n : Pts Y σ → ℝ) (V V' : Y.X.affineOpens) (t : Γ(Y.X, V.1)) (t' : Γ(Y.X, V'.1)) (f f' : Pts Y σ → ℝ), (∃ y : Y.X, y ∉ C) → (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t} → (Scheme.IdealSheafData.vanishingIdeal C).ideal V' = Ideal.span {t'} → (Y.an σ).SmoothOn (ptsIn Y.str σ V.1) f → (Y.an σ).SmoothOn (ptsIn Y.str σ V'.1) f' → (∀ z ∈ ptsIn Y.str σ V.1, n z ^ 2 = ‖ev Y.str σ V.1 t z‖ ^ 2 * Real.exp (-f z)) → (∀ z ∈ ptsIn Y.str σ V'.1, n z ^ 2 = ‖ev Y.str σ V'.1 t' z‖ ^ 2 * Real.exp (-f' z)) → ∀ y₀ ∈ ptsIn Y.str σ V.1 ∩ ptsIn Y.str σ V'.1, ∃ W : Set (Pts Y σ), IsOpen W ∧ y₀ ∈ W ∧ ∃ G : Pts Y σ → ℂ, (Y.an σ).HoloOn W G ∧ ∀ z ∈ W ∩ ptsIn Y.str σ V.1 ∩ ptsIn Y.str σ V'.1, f z - f' z = (G z).re := by
  first | exact @GlobalTheory.DivSec.sub_eq_re_of_eqns | exact GlobalTheory.DivSec.sub_eq_re_of_eqns | (intros; apply GlobalTheory.DivSec.sub_eq_re_of_eqns <;> assumption)
