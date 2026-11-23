import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proper_semiAbelian_family' : ∀ (g n : ℕ), n.Prime → Odd n → ∃ a : ℕ, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R₀ : Subalgebra o Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) → ∀ (P : Out.PolAV (Sp Ω)) (ze : oˣ), P.g = g → IsUnit (n : o) → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → Nonempty (Out.Level P (n ^ a) (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Z : Scheme.{0}) (s : Z ⟶ Sp o) (x : Sp Ω ⟶ Z) (G : Over Z) (_ : GrpObj G) (φ : P.A.left ⟶ G.left), IsProper s ∧ x ≫ s = spMap (algebraMap o Ω) ∧ IsSemiAbelian G ∧ IsGrpPullback P.A G x φ := by
  first | exact @GlobalTheory.exists_proper_semiAbelian_family | exact GlobalTheory.exists_proper_semiAbelian_family | (intros; apply GlobalTheory.exists_proper_semiAbelian_family <;> assumption)
