import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessTangentFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_witness_tangent_family : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (m : ℕ) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (eig : (epsR (PowerSeries A) ⟶ W.t.G) → Prop), (∀ w, eig w ↔ ∀ x : 𝓞 E, (w ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ w.left) → (∀ k, LieImg W (e k) (v k)) → (∀ k, IsTangent (v k) ∧ eig (v k)) → ((∀ w, IsTangent w → eig w → ∃! cf : Fin m → PowerSeries A, IsLieComb cf v w) ↔ ∀ ν w, LieImg W ν w → IsTangent w → eig w → ∃! cf : Fin m → A, GtComb cf e ν) := by
  first | exact @GlobalTheory.ConstEig.basis_iff_const | exact GlobalTheory.ConstEig.basis_iff_const | (intros; apply GlobalTheory.ConstEig.basis_iff_const <;> assumption)
