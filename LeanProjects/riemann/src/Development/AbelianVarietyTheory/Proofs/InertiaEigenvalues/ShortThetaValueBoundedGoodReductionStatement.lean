import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShortThetaValueBoundedGoodReduction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaValue_bounded_goodReduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (n d N : ℕ) (La : GenLat E n) (w : (Fin n → LevQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (v : T.Fr), Good y → La.Unimod → La.TrivAt l.M → La.LevOK N l.M → (∀ q, InV T (io (w q))) → P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) → P.IsHomogeneous d → (∀ m, InV T (io (P.coeff m))) → (letI := io.toAlgebra; thLaValAt Xo c nab w La N P y.1 v) → InV T (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l) : ℕ) : T.Fr) * ((2 * NumberField.discr E * N : ℤ) : T.Fr) ^ d * v) := by
  first | exact @GlobalTheory.GoodThetaBound.theta_value_bounded | exact GlobalTheory.GoodThetaBound.theta_value_bounded | (intros; apply GlobalTheory.GoodThetaBound.theta_value_bounded <;> assumption)
