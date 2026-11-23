import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSupNormLocalRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_sup_norm_local_rescale : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (ε : GlobalTheory.TrueGeo.Ext v) (θ : K →+* AlgebraicClosure F) (𝔞 : Submodule (𝓞 K) K), 𝔞.FG → 𝔞 ≠ ⊥ → (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (⨆ a : 𝔞, ‖((ioOf (resP v) ε).comp θ) a‖) = Real.log (⨆ a : 𝔞, ε.w (θ a)) := by
  first | exact @GlobalTheory.LieSmooth.log_iSup_w_eq_mul_log_iSup_norm | exact GlobalTheory.LieSmooth.log_iSup_w_eq_mul_log_iSup_norm | (intros; apply GlobalTheory.LieSmooth.log_iSup_w_eq_mul_log_iSup_norm <;> assumption)
