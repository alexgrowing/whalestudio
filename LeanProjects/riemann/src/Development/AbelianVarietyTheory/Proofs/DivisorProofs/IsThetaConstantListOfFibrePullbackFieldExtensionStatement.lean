import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  first | exact @GlobalTheory.UMin.ThPull.thList_pull | exact GlobalTheory.UMin.ThPull.thList_pull | (intros; apply GlobalTheory.UMin.ThPull.thList_pull <;> assumption)
