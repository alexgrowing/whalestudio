import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUltrametricNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_ultrametric_norm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} [X.IsSeparated] (t : SAB H X) {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G), TanBasis t b → ∀ {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {xC : Sp C ⟶ X} (hC : spMap j ≫ xK = xC), TanIndep t (fun i => bcTan j hC (b i)) ∧ ∀ w, w ∈ latDR t xC ↔ ∃ d ∈ latC j (lieCoordLat t hx b), w = combLeft t (fun i => bcTan j hC (b i)) d := by
  first | exact @GlobalTheory.LatDRSpan.latDR_eq_latC | exact GlobalTheory.LatDRSpan.latDR_eq_latC | (intros; apply GlobalTheory.LatDRSpan.latDR_eq_latC <;> assumption)
