import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistTypeDet

open Classical in

theorem detChar_eq_one_of_suppAt : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  intro D S T B hB _ A _ t ht hadm u κ hlift hsupp
  have hst : Lev.finE T κ ∈ St B.F.βT := Formalism.L2.DIV.parLev_St hlift.2.1
  rw [GlobalTheory.TwistDetStabAll.detChar_eq_prod_res B hB t ht hlift.1 hst]
  refine Finset.prod_eq_one fun PP hPP => ?_
  obtain ⟨P, hPg, hQ, hsplit⟩ := hadm.1.split
  have hnot : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.mp hadm.1.disj h (Finset.mem_union_right _ hPP)
  rw [GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT hsplit hPg (hQ (Finset.mem_union_right _ hPP)) hnot hst hsupp,
    map_one, map_one]

end GlobalTheory.TwistTypeDet
