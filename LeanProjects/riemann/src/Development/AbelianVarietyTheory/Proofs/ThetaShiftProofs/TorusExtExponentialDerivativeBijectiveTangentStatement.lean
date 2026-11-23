import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), (∀ ν, GtTanR ν → ∃! z₀, AnVec Ha ν z₀) ∧ (∀ z₀, ∃! ν, AnVec Ha ν z₀) ∧ (∀ ν z₀, AnVec Ha ν z₀ → GtTanR ν) ∧ ∀ (m : ℕ) (cf : Fin m → ℂ) (e : Fin m → Out.GtPt a.D₀ (epsR ℂ)) (z : Fin m → (Fin g → ℂ)) ν, (∀ i, AnVec Ha (e i) (z i)) → (GtComb cf e ν ↔ AnVec Ha ν (∑ i, cf i • z i)) := by
  first | exact @GlobalTheory.ExpTan.anVec_bijective | exact GlobalTheory.ExpTan.anVec_bijective | (intros; apply GlobalTheory.ExpTan.anVec_bijective <;> assumption)
