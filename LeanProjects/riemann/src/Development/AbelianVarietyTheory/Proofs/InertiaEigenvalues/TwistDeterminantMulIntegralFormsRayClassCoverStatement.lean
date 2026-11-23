import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDeterminantMulIntegralFormsRayClassCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistDeterminant_mul_integralForms_rayClassCover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ C : Cover T j T.σ₀, C.IsUnif → (∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M) → ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist C.σ₂ C.d.pd xi → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), ∀ φ ∈ C.intForms wa n S, (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) : ℂˣ) : ℂ) * φ g) ∈ C.intForms wa n S := by
  first | exact @GlobalTheory.TwistInt.mul_twist_mem_intForms | exact GlobalTheory.TwistInt.mul_twist_mem_intForms | (intros; apply GlobalTheory.TwistInt.mul_twist_mem_intForms <;> assumption)
