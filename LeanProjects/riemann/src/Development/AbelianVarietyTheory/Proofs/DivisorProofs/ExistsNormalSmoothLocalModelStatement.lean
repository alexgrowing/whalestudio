import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalSmoothLocalModel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_smooth_local_model : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (y : (Φ.C k).Y.X), ∃ (W : (Φ.C k).Y.X.Opens) (T : Scheme.{0}) (h : W.toScheme ⟶ T) (g : T ⟶ gen s.T.Z), y ∈ W ∧ Smooth g ∧ LocallyOfFiniteType g ∧ IsIntegral T ∧ (∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)) ∧ h ≫ g = W.ι ≫ (Φ.C k).π ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), ∃! x : Spec (.of Ω) ⟶ W.toScheme, x ≫ h = t := by
  first | exact @GlobalTheory.ShFam.Cell.exists_cell_nhds | exact GlobalTheory.ShFam.Cell.exists_cell_nhds | (intros; apply GlobalTheory.ShFam.Cell.exists_cell_nhds <;> assumption)
