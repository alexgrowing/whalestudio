import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrincipalPolarisationAbelianFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarisation_abelianFibre : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  first | exact @GlobalTheory.ZH.UFib.exists_pol | exact GlobalTheory.ZH.UFib.exists_pol | (intros; apply GlobalTheory.ZH.UFib.exists_pol <;> assumption)
