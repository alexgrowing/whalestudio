import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_potential_isSNC_boundary : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y σ → ℝ) (hn : ∀ i, IsDivNorm (Y.an σ) (C i) (n i)) (B : FinHolAtlas Y.dim (Pts Y σ)), IsAlgAtlas B → (∀ y : Y.X, LSncAt Y.X C y) → IsSNC B (GlobalTheory.DivSec.divPot hn) (GlobalTheory.DivSec.divSec hn) (fun _ : Fin m => 1) (fun i => {z | LiesIn z (C i)}) := by
  first | exact @GlobalTheory.DivSec.isSNC_divSec | exact GlobalTheory.DivSec.isSNC_divSec | (intros; apply GlobalTheory.DivSec.isSNC_divSec <;> assumption)
