import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfActsTriviallyAbelianVarietyAlgClosure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_acts_trivially_abelianVariety_algClosure : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (x : O), (OAct.pullback (spMap (algebraMap K (AlgebraicClosure Ω))) A α).act x = 1 → x = 0 := by
  first | exact @GlobalTheory.ActTrivialInj.eq_zero_of_act_pullback_eq_one | exact GlobalTheory.ActTrivialInj.eq_zero_of_act_pullback_eq_one | (intros; apply GlobalTheory.ActTrivialInj.eq_zero_of_act_pullback_eq_one <;> assumption)
