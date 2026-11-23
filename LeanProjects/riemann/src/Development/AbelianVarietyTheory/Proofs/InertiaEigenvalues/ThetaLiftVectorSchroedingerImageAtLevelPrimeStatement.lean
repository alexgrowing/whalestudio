import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  first | exact @GlobalTheory.BadPlace.vec_read_at | exact GlobalTheory.BadPlace.vec_read_at | (intros; apply GlobalTheory.BadPlace.vec_read_at <;> assumption)
