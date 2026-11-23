import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDescends
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_descends : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}, X₀.IsPullBy X b i →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), ∃ t₀ : Sp Ω ⟶ S₀, t₀ ≫ b = t) →
    ∀ {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A)), (∀ k, q k ^ N = 1) →
    (∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) → Nonempty (X.Level N) := by
  first | exact @GlobalTheory.RealMult.level_descend | exact GlobalTheory.RealMult.level_descend | (intros; apply GlobalTheory.RealMult.level_descend <;> assumption)
