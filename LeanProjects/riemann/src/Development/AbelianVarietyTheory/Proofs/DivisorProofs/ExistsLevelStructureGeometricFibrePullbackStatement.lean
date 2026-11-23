import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureGeometricFibrePullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_structure_geometric_fibre_pullback : ∀ (T K : Type) [CommRing T] [IsNoetherianRing T] [Field K] [IsAlgClosed K] (χ : T →+* K) (P : PolAV (Sp T)) (Q : PolAV (Sp K)) (ψ : Q.A.left ⟶ P.A.left), IsGrpPullback Q.A P.A (spMap χ) ψ → LBIso Q.L (P.L.pull ψ) → ∀ (g M : ℕ) (hg : Q.g = g) (c : Tˣ) (ζK : Kˣ), (M : K) ≠ 0 → Units.map χ.toMonoidHom c = ζK → IsPrimitiveRoot ζK M → ∀ (y : Fin (2 * g) → (baseOver (Sp T) ⟶ P.A)), (∀ i, y i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (y i) (y j) (unitOn c ^ stdSymp g i j)) → ∃ lev : Level Q M (unitOn ζK), ∀ i, (GlobalTheory.levelBasis lev hg i).left ≫ ψ = spMap χ ≫ (y i).left := by
  first | exact @GlobalTheory.Mum.FibLevel.exists_level_of_pullback | exact GlobalTheory.Mum.FibLevel.exists_level_of_pullback | (intros; apply GlobalTheory.Mum.FibLevel.exists_level_of_pullback <;> assumption)
