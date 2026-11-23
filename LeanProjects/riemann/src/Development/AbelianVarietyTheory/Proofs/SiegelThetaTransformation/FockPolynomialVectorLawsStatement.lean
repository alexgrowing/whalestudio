import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
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
theorem _root_.GlobalTheory.T.fockPolynomialVector_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∀ f, C.IsTh f → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.IsTh (pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q) ∧ (∀ v, pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f (MvPolynomial.X v * Q) = aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS B v (pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q)) ∧ pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f 1 = f ∧ (∀ f', C.IsTh f' → C.fvec B (f + f') Q = C.fvec B f Q + C.fvec B f' Q) ∧ (∀ a : ℂ, C.fvec B (a • f) Q = a • C.fvec B f Q) ∧ ∀ u, IsFinPt u → C.fvec B (C.rho u f) Q = C.rho u (C.fvec B f Q) := by
  first | exact @GlobalTheory.Ker.FockAlg.fock_vec_laws | exact GlobalTheory.Ker.FockAlg.fock_vec_laws | (intros; apply GlobalTheory.Ker.FockAlg.fock_vec_laws <;> assumption)
