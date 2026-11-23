import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseStableUnderPullbackOfData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromBase_stable_under_pullback_of_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (Q : DegPre R) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* R) (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (hD : IsPullDeg θ Q Q') (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ y, e' y = e (hD.xe y)) → (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (oQ.onB.act x)) → (∀ k, θ (s k) ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' (θ.comp iw) (fun k => θ (s k)) ε e' := by
  first | exact @GlobalTheory.UCanon.DivFromPull.divFrom_pull | exact GlobalTheory.UCanon.DivFromPull.divFrom_pull | (intros; apply GlobalTheory.UCanon.DivFromPull.divFrom_pull <;> assumption)
