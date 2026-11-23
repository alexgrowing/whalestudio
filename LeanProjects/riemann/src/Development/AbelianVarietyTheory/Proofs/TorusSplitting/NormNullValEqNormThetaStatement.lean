import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormNullValEqNormTheta
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_nullVal_eq_norm_theta_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ) (y : FrPt Xo c (CAt σ)), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → y.x = Fu.u i Pm → IsFnOf Fu i Pm fr y.x y.s θ → ∀ (N : ℕ), Odd N → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (z : Fin g → ℂ) (w : CAt σ), p ^ (N ^ 2) = 1 → p.left = (Fu.ex i Pm z).left → IsNullVal Xo c N y p w → ‖toC w‖ = ‖θ ((N : ℂ) • z)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm ((N : ℂ) • z) ((N : ℂ) • z)).re) := by
  first | exact @GlobalTheory.norm_nullVal_eq_norm_theta | exact GlobalTheory.norm_nullVal_eq_norm_theta | (intros; apply GlobalTheory.norm_nullVal_eq_norm_theta <;> assumption)
