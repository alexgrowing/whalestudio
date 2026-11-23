import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBelowPointDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_below_point_decomposition : ∀ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (A : Adl C Y) {K : Type} [Field K] [NumberField K] (φ : F →+* K) (p : Sp K ⟶ Y.X) (hp : p ≫ Y.str = spMap φ), A.ht (below p) = -((∑ σ : K →+* ℂ, (Real.log (C.pn Y (σ.comp φ) A.D (A.m _) (C.cx Y _ ((eqn A.D (below p))⁻¹ : Y.Fnˣ)) (cxPtOf p hp σ)) / 2 - (A.n : ℕ) * A.ci (InfinitePlace.mk (σ.comp φ)))) + ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, A.lg v (extOf v) (algPtOf p hp θ)) / (((A.n : ℕ) : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  first | exact @GlobalTheory.LieSmooth.HtEmb.main | exact GlobalTheory.LieSmooth.HtEmb.main | (intros; apply GlobalTheory.LieSmooth.HtEmb.main <;> assumption)
