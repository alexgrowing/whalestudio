import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRoot
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
theorem _root_.GlobalTheory.T.commutatorPairing_spread_points_eq_spread_root : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  first | exact @GlobalTheory.MumPair.weilIs_of_spread | exact GlobalTheory.MumPair.weilIs_of_spread | (intros; apply GlobalTheory.MumPair.weilIs_of_spread <;> assumption)
