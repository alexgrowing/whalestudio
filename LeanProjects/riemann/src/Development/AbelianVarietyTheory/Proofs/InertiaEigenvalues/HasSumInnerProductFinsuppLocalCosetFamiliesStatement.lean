import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerProductFinsuppLocalCosetFamilies
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_innerProduct_finsupp_localCosetFamilies : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LevProd R i → TransLaws R i → FinMult R i t → LevFix R i t → VecNe R i t → FinSum R i t → ∀ th, IsRaw R i t th → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y, HasSum (fun F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite} => (a : ℂ) * ((∏ᶠ v, Eu.acoef R i t μ 𝓕 v (F.1 v)) * ⟪x, Eu.Bfam R i F.1 y⟫_ℂ)) ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.FamSum.hasSum_families | exact GlobalTheory.RawLift.FamSum.hasSum_families | (intros; apply GlobalTheory.RawLift.FamSum.hasSum_families <;> assumption)
