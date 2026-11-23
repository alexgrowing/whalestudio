import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_fractional_ideal : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (φ : F →+* K) (𝔞 : Submodule (𝓞 K) K), 𝔞.FG → 𝔞 ≠ ⊥ → (Function.support fun v : HeightOneSpectrum (𝓞 F) => ∑ θ : EmbOver φ, Real.log (⨆ a : 𝔞, (extOf v).w (θ.1 a))).Finite ∧ ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, Real.log (⨆ a : 𝔞, (extOf v).w (θ.1 a)) = idealLog 𝔞 := by
  first | exact @GlobalTheory.LieSmooth.finsum_sum_log_iSup_eq_idealLog | exact GlobalTheory.LieSmooth.finsum_sum_log_iSup_eq_idealLog | (intros; apply GlobalTheory.LieSmooth.finsum_sum_log_iSup_eq_idealLog <;> assumption)
