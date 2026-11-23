import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_sec_of_eff {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (h : Eff (cls N hN)) :
    ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  obtain ⟨N', hN', hc, σ, j, hj⟩ := h
  obtain ⟨w, hw⟩ := (cls_eq_iff hN' hN).1 hc
  let e : LB.Sec N' ≃ₗ[Γ(X, ⊤)] LB.Sec N :=
    (SecOn.topEquiv N').symm ≪≫ₗ SecOn.congr hN' hN w hw ⊤ ≪≫ₗ SecOn.topEquiv N
  have hσ : σ ≠ 0 := fun h0 => hj (by rw [h0]; rfl)
  have he : e σ ≠ 0 := by
    intro h0
    exact hσ (e.injective (h0.trans (map_zero e).symm))
  by_contra hne
  push_neg at hne
  exact he (HighTwist.sec_eq_zero _ (hne (e σ)))

end GlobalTheory.EffBound
