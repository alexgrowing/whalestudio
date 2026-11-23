import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnits
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_descent_of_units : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f → ∀ V : Q.Opens,
    Function.Injective (pullU f V) ∧ ∀ a : Γ(P, f ⁻¹ᵁ V)ˣ,
      (∀ (W : Scheme.{0}) (b c : W ⟶ P), b ≫ f = c ≫ f → ∀ w : W, f (b w) ∈ V →
        gm b w (f ⁻¹ᵁ V) a = gm c w (f ⁻¹ᵁ V) a) → ∃ s : Γ(Q, V)ˣ, pullU f V s = a := by
  first | exact @GlobalTheory.CompanionTheory.FnDesc.units_descend | exact GlobalTheory.CompanionTheory.FnDesc.units_descend | (intros; apply GlobalTheory.CompanionTheory.FnDesc.units_descend <;> assumption)
