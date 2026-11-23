import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformised
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised : ∀ (R V' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : R →+* V'), IsCN R → IsCN V' → IsLocalHom θ → ∀ (Q : Data R) (W : (Sp R).Opens) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsSemiAbelian G₁ → CanonOn Q W G₁ P → spMap θ (genericPoint (Sp V')) ∈ W → ∀ (D' : DegData V' (maximalIdeal V')) (ex : D'.toPre.X ≃+ Q.X), PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.canon_pull_unif | exact GlobalTheory.Mum.canon_pull_unif | (intros; apply GlobalTheory.Mum.canon_pull_unif <;> assumption)
