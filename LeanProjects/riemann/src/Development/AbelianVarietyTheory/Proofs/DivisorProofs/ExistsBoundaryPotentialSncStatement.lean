import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundaryPotentialSnc
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boundary_potential_snc : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y (I.ε a) → ℝ), Y.dim = e → (∀ y : Y.X, LSncAt Y.X C y) → (∀ i, IsDivNorm (Y.an (I.ε a)) (C i) (n i)) → (∀ z, z ∈ M.Z a ↔ ∃ i, under (I.pt a z) ∈ C i) → (∀ z, z ∉ M.Z a → M.r a z = Real.exp 1 - Real.log ((∏ i, n i (I.pt a z)) ^ 2)) → ∃ (L : LocPot (M.X a)) (t : M.X a → M.X a → ℂ), IsBdSec (M.A a) (M.Z a) (M.r a) L t ∧ IsSNC (M.A a) L t (fun _ : Fin m => 1) fun i => {z | under (I.pt a z) ∈ C i} := by
  first | exact @GlobalTheory.DivSec.bdSec_of_divNorm | exact GlobalTheory.DivSec.bdSec_of_divNorm | (intros; apply GlobalTheory.DivSec.bdSec_of_divNorm <;> assumption)
