import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem countable_numberField_type (K : Type) [Field K] [NumberField K] : Countable K := by
  let b := Module.finBasis ℚ K
  exact (b.equivFun.toEquiv.injective).countable

theorem lag_countable : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  intro D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  let M := (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)
  haveI : Countable (Submodule D.host.E M) := by
    have hs : Function.Surjective (fun s : Finset M => Submodule.span D.host.E (s : Set M)) := by
      intro N
      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
      exact ⟨s, hs⟩
    exact hs.countable
  unfold Lag
  infer_instance

end GlobalTheory.RawLift
