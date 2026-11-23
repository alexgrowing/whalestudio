import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanTranslatesConjugateHalfTwistPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_translates_conjugateHalf_twistPlace : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), T.rank ≤ S.rank → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ N : ℕ, IsBaseFrame S βS ΛS N → Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∀ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ, ξ PP ≠ 1 → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → (∀ κ : GA D S, SuppAt e S κ → κ ∈ GfC S → finE S κ ∈ St βS → redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) → (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) → ∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → Φ (actO S T κ 1 x) * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) x' = Φ x * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) (actO S T κ 1 x')) → Φ ∈ Submodule.span ℂ (translT S T (cA D e) (adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)))) := by
  first | exact @GlobalTheory.DownLift.ConjHalfGen.mem_span_translT | exact GlobalTheory.DownLift.ConjHalfGen.mem_span_translT | (intros; apply GlobalTheory.DownLift.ConjHalfGen.mem_span_translT <;> assumption)
