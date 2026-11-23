import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSncPullbackSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_snc_pullback_smooth : ∀ (k : Type) [Field k] [CharZero k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) [Smooth p] (π : Y ⟶ X) [Smooth π] (m : ℕ) (C : Fin m → Closeds X) (y : Y), LSncAt X C (π y) → LSncAt Y (fun i => (C i).preimage π.continuous) y := by
  first | exact @GlobalTheory.SncPull.lsncAt_preimage | exact GlobalTheory.SncPull.lsncAt_preimage | (intros; apply GlobalTheory.SncPull.lsncAt_preimage <;> assumption)
