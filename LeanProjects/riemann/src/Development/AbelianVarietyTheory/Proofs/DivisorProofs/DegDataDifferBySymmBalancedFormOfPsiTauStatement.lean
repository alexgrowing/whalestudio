import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataDifferBySymmBalancedFormOfPsiTau
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degData_differ_by_symmBalancedForm_of_psi_tau : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W V : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing V] [IsDomain V] [IsLocalRing V] (θ₀ : W →+* V) (D₀ : DegPre W) [Module (𝓞 E) D₀.X] (o₀ : letI := H.starRing; D₀.OAct (𝓞 E)) (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (e : Q.X ≃ₗ[𝓞 E] D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → (letI := H.starRing; TraceFormTwistIso D₀ o₀ H.w0) → Q.TauBimult → (letI := H.starRing; TraceFormTwistIso Q oQ H.w0) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (oQ.onB.act a).left ≫ β = β ≫ (o₀.onB.act a).left) → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)) (q : Q.X → Q.X → (FractionRing V)ˣ), (∀ y : Q.X, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ (∀ y, PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ) ∧ (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) ∧ ∀ y, (g y)⁻¹ = q y (H.w0 • y) := by
  first | exact @GlobalTheory.YRatio.main | exact GlobalTheory.YRatio.main | (intros; apply GlobalTheory.YRatio.main <;> assumption)
