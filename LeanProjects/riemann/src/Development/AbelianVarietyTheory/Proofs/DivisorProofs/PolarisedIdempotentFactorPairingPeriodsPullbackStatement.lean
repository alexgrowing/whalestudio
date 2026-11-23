import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPairingPeriodsPullback
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
theorem _root_.GlobalTheory.T.polarisedIdempotentFactor_pairing_periods_pullback : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X), PullData Q θ Q' ex → ∃ β : Q'.B.left ⟶ Q.B.left, IsGrpPullback Q'.B Q.B (spMap θ) β ∧ (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) ∧ ∀ (inc : Q'.B ⟶ D₁.P.A) (xi : Q'.X →+ D₁.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left → (∀ y, hD.xe (xi y) = F.xi (ex y)) → (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) → ∃ w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ D₁.P.A D₁.P.L).pull (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D₁.P.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' = lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' * val (D₁.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.FactorTau.factor_tau_pull | exact GlobalTheory.FactorTau.factor_tau_pull | (intros; apply GlobalTheory.FactorTau.factor_tau_pull <;> assumption)
