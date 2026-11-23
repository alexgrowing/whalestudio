import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFock
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_rationalPoints_thetaFunctions_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, C.IsTh f → ∀ w, om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ ∀ (ga : GL (Fin T.rank) D.host.E) (γ : GA D T), IsRatOf T ga γ → ∀ φ : TF S.rank C.g, SW.IsSB φ → (∀ x ∈ C.X.dom, om (1, γ) (C.Th x φ) = C.Th (lact ga x) (wG C.X C.bas C.idx ga φ)) ∧ ∀ B, C.IsB B → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (1, γ) (C.fvec B (C.Th (C.xB B) φ) Q) = C.fvec (C.mvB γ B) (C.Th (C.xB (C.mvB γ B)) (wG C.X C.bas C.idx ga φ)) Q := by
  first | exact @GlobalTheory.Ker.OmRat.om_rat | exact GlobalTheory.Ker.OmRat.om_rat | (intros; apply GlobalTheory.Ker.OmRat.om_rat <;> assumption)
