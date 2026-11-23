import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

def Eff {X : Scheme.{0}} (c : Pic X) : Prop :=
  ∃ (N : LB X) (hN : N.IsLB), cls N hN = c ∧ ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0

theorem eff_of_sec {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (σ : LB.Sec N) (j : N.ι) (h : σ.f j ≠ 0) :
    Eff (cls N hN) :=
  ⟨N, hN, rfl, σ, j, h⟩

theorem cls_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) :
    cls (pw H t) (isLB_pw hH t) = t • cls H hH := by
  have hL := LB.isLB_linComb hH (fun _ : PUnit => 𝟙 X) (fun _ => t)
  have e : LBIso (LB.LinComb H (fun _ : PUnit => 𝟙 X) (fun _ => t)) (pw H t) :=
    iso_of_chart (isLB_pw hH t)
      { idx := fun j => j PUnit.unit
        le := fun j y hy => Set.mem_iInter.1 hy PUnit.unit
        g := fun y j j' hj hj' => by
          refine (gm_linComb H (fun _ : PUnit => 𝟙 X) (fun _ => t) (𝟙 X) y j j' hj hj').trans ?_
          rw [Fintype.prod_unique]
          change _ = gm (𝟙 X) y _ (H.g (j PUnit.unit) (j' PUnit.unit) ^ t)
          rw [map_zpow, Category.comp_id] }
  rw [← (cls_eq_iff hL (isLB_pw hH t)).2 e, cls_linComb hH, Fintype.sum_unique, pull_id]

end GlobalTheory.EffBound
