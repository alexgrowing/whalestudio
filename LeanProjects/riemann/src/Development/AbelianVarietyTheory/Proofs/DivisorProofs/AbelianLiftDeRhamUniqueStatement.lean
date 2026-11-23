import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftDeRhamUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_lift_crystalline_comparison : GlobalTheory.Published.GrothendieckDeformation → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I),
    IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
      (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (O : Type) [CommRing O] (a₀ : OAct O A₀), (∀ (x : O), ∀ d ∈ liftFil κ h, act κ (spMap π) a₀ x d ∈ liftFil κ h) →
      ∃ a : OAct O A, ∀ x, (a₀.act x).left ≫ i = i ≫ (a.act x).left := by
  first | exact @GlobalTheory.OActLift.exists_oAct_lift | exact GlobalTheory.OActLift.exists_oAct_lift | (intros; apply GlobalTheory.OActLift.exists_oAct_lift <;> assumption)
