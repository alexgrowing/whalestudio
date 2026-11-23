import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeRepresentativesRightTranslateIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOfCfEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeRepresentatives_rightTranslate_identity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), TransLaws R i → ∀ (B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)), (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) → (∀ v α, GlobalTheory.UpInj.cf (Wc D i) v α = α → ∃ C, GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C) ∧ (∀ v α C, GlobalTheory.UpInj.cf (Wc D i) v α = α → GlobalTheory.UpInj.DCRep (GlobalTheory.UpInj.cf (Wc D i) v) (GlobalTheory.UpInj.KR R i) α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) := by
  first | exact @GlobalTheory.UpInj.heckeReps | exact GlobalTheory.UpInj.heckeReps | (intros; apply GlobalTheory.UpInj.heckeReps <;> assumption)
