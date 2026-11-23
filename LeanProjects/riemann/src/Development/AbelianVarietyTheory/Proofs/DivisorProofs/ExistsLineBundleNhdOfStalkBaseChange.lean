import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLB

set_option backward.isDefEq.respectTransparency false

theorem exists_lb_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (N : LB (pullback h (S.fromSpecStalk x))), N.IsLB →
    ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(h ⁻¹ᵁ W), N'.IsLB ∧
      ∀ a : pullback h (S.fromSpecStalk x) ⟶ ↑(h ⁻¹ᵁ W),
        a ≫ (h ⁻¹ᵁ W).ι = pullback.fst h (S.fromSpecStalk x) → LBIso (N'.pull a) N := by
  intro S X _ h _ _ x N hN
  have hpb := IsPullback.of_hasPullback h (S.fromSpecStalk x)
  have hlim : IsLimit (GlobalTheory.schemeConeOfFamily (GlobalTheory.StalkLimit.diagram x h)
      (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f)) :=
    (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  have hcpt : ∀ V : GlobalTheory.StalkLimit.AffNhd x, CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V.1.ι)
  have hqs : ∀ V : GlobalTheory.StalkLimit.AffNhd x,
      QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V.1.ι)
  obtain ⟨j, M, hM, -, hall⟩ := GlobalTheory.LBLimit.exists_lb_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hlim N hN
  refine ⟨j.1, j.2.1, M.pull (pullbackRestrictIsoRestrict h j.1).inv, pull_isLB hM _, fun a ha => ?_⟩
  refine LBIso.symm (hall _ a (pullbackRestrictIsoRestrict h j.1).inv ?_)
  have hfst : (GlobalTheory.StalkLimit.cone hpb).π.app j ≫ pullback.fst h j.1.ι =
      pullback.fst h (S.fromSpecStalk x) := GlobalTheory.StalkLimit.cone_π_fst hpb j
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRestrictIsoRestrict_inv_fst, ha, hfst]
  · rw [← cancel_mono j.1.ι]
    simp only [Category.assoc]
    rw [← pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc, reassoc_of% ha,
      reassoc_of% hfst]

end GlobalTheory.StalkLB
