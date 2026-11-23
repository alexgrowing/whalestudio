import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionTheta

theorem exists_theta_acts : KerPowSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] (t : Spec (CommRingCat.of F) ⟶ S) (n : ℕ), 1 ≤ n → ∀ x : Over.mk t ⟶ P.A, x ^ n = 1 → ∃ θ : ThetaGrp P.A P.L (n : ℤ) (Over.mk t), θ.pt = x ∧ ∀ s : LB.Sec (LPow P.A P.L (n : ℤ) (Over.mk t)), ∃ s', IsActOf P.A P.L (n : ℤ) θ s s' := by
  intro hK S _ P F _ t n hn x hx

  have : Unique (Over.mk t).left := inferInstanceAs (Unique (PrimeSpectrum F))
  obtain ⟨θ, hθ⟩ := GlobalTheory.BoxTheta.exists_theta hK P hn x hx

  exact ⟨θ, hθ, fun s => GlobalTheory.VVRank.exists_isTwistPull P.A P.isLB θ.isGen s⟩

end GlobalTheory.TorsionTheta
