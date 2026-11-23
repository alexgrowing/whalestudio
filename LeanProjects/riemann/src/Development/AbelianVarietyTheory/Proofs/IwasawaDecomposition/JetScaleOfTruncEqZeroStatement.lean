import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetScaleOfTruncEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetScale_of_trunc_eq_zero : ∀ {S : Type} [CommRing S] {ρ : Type} (m : ℕ) (c : S) (p : Jet S ρ (m + 1)),
    (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) p = 0 → jetScale (fun _ => c) p = c ^ (m + 1) • p := by
  first | exact @GlobalTheory.JetScaleTop.jetScale_top | exact GlobalTheory.JetScaleTop.jetScale_top | (intros; apply GlobalTheory.JetScaleTop.jetScale_top <;> assumption)
