import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChart
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_weil_open_chart : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion x] (κ : FractionRing R ≃+* Ω), spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ → ∀ (T : Type) [CommGroup T] [Finite T] (Γ : BT.QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x n i → ∀ (L₀ : Type) [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E), (∀ v, (M.pt (j v)).left = spMap (dualMap (κ.toRingHom.comp (algebraMap R _))) ≫ (M₀.pt v).left) → ∀ (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E), y ^ n = 1 → (∀ (t : T) (g : Over.mk ξ ⟶ G), spMap κ.toRingHom ≫ (Γ.pt t).left ≫ i = g.left → κ (algebraMap R _ (χ t : R)) = e y g) → Γ.IsHT i M₀ n χ w₀ → (∀ v, w (j v) = κ (algebraMap R _ (w₀ v))) → ∀ q : Cpt ξ, q.1 ∈ Set.range x → M.IsHTAt L n y q w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT | exact GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT | (intros; apply GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT <;> assumption)
