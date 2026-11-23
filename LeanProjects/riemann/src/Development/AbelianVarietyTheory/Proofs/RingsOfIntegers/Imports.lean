import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullExp
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePullExpands
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpandsPullOne

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t) (a : 𝓞 E) (N k : ℕ), (letI := H.starRing; a * star a = (N : 𝓞 E)) → 0 < N → 0 < k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ (s' : P.U.SecK (k * N)), IsPullByEnd P.U (t.act.act a) k N s s' → letI := H.starRing; ∃ (F' : Fam P.D.toPre (FractionRing V) (k * N)) (ζ : FractionRing V) (m : ℕ), 0 < m ∧ ζ ^ m = 1 ∧ PullAl P.D (FractionRing V) P.oD a k N F F' ∧ P.U.Expands (k * N) s' (ζ • F') := by
  intro V _ _ _ _ _ E _ _ _ H t P a N k hN hN0 hk s F hs s' hs'
  obtain ⟨F', h₁, h₂⟩ := GlobalTheory.PullEveryLevel.expands_pull_every_level GlobalTheory.abelianSchemeLaws_all.1 P a N hN hN0 hk
    s F hs s' hs'
  exact ⟨F', 1, 1, Nat.one_pos, one_pow 1, h₂, by rw [one_smul]; exact h₁⟩

end GlobalTheory.ExpandsPullOne
