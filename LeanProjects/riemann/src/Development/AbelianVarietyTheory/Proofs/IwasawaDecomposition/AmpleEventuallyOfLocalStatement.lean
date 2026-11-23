import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleEventuallyOfLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_eventually_of_local : ∀ {F : Type} [Field F] (Y : Var F) {S T : Scheme.{0}} (f : Y.X ⟶ S) (g : S ⟶ T), IsAffineHom g → ∀ (H : LB T), IsAmpleLB H → ∀ (Δ Λ : Y.Dv), LBIso (Y.lb Δ) (H.pull (f ≫ g)) → (∀ z : S, ∃ V : S.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB ((Y.lb Λ).pull (f ⁻¹ᵁ V).ι)) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Y.ample (n • Δ + Λ) := by
  first | exact @GlobalTheory.AmpleTwistBase.ample_nsmul_add | exact GlobalTheory.AmpleTwistBase.ample_nsmul_add | (intros; apply GlobalTheory.AmpleTwistBase.ample_nsmul_add <;> assumption)
