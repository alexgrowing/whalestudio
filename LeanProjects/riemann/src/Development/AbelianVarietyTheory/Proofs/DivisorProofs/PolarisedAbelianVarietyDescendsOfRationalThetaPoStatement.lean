import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianVarietyDescendsOfRationalThetaPo
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianVariety_descends_of_rational_thetaPoints : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n : ℕ), n.Prime → Odd n → (∀ j : ℕ, 1 ≤ j → ∃ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ IsThetaPt A (n ^ j) x fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (A₀ : PolAV (Sp F)) (a : A.A.left ⟶ A₀.A.left), IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  first | exact @GlobalTheory.ThetaDescent.descends | exact GlobalTheory.ThetaDescent.descends | (intros; apply GlobalTheory.ThetaDescent.descends <;> assumption)
