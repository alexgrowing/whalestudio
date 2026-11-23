import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealEmbeddingsLinearlyIndependent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_embeddings_linearly_independent : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := by
  first | exact @GlobalTheory.realEmb_linearIndependent_on_integers | exact GlobalTheory.realEmb_linearIndependent_on_integers | (intros; apply GlobalTheory.realEmb_linearIndependent_on_integers <;> assumption)
