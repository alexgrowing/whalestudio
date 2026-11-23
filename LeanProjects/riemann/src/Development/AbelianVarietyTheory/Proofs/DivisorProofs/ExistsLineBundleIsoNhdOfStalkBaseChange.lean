import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLBIso

set_option backward.isDefEq.respectTransparency false

theorem lbIso_pull_iff {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) :
    LBIso (A.pull f) (B.pull f) ↔
      CechPic.pull f (CechPic.cls A hA) = CechPic.pull f (CechPic.cls B hB) := by
  rw [← CechPic.cls_pull hA f (pull_isLB hA f), ← CechPic.cls_pull hB f (pull_isLB hB f)]
  exact (CechPic.cls_eq_iff _ _).symm

theorem exists_lbIso_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (A B : LB X), A.IsLB → B.IsLB →
    LBIso (A.pull (pullback.fst h (S.fromSpecStalk x))) (B.pull (pullback.fst h (S.fromSpecStalk x))) →
    ∃ W : S.Opens, x ∈ W ∧ LBIso (A.pull (h ⁻¹ᵁ W).ι) (B.pull (h ⁻¹ᵁ W).ι) := by
  intro S X _ h _ _ x A B hA hB hAB

  have hpb : IsPullback (pullback.fst h (S.fromSpecStalk x)) (pullback.snd h (S.fromSpecStalk x)) h
      (S.fromSpecStalk x) := IsPullback.of_hasPullback _ _
  have hc := (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  obtain ⟨V₀⟩ : Nonempty (GlobalTheory.StalkLimit.AffNhd x) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V₀.1.ι)
  have : QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V₀.1.ι)

  have h0 : LBIso ((A.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀))
      ((B.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀)) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.cone_π_fst, ← lbIso_pull_iff hA hB]
    exact hAB

  obtain ⟨j, f, hj⟩ := GlobalTheory.exists_lbIso_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hc
    (A.pull (pullback.fst h V₀.1.ι)) (B.pull (pullback.fst h V₀.1.ι)) (pull_isLB hA _) (pull_isLB hB _) h0
  have hj' : CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls A hA) =
      CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls B hB) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.diagram_map_fst] at hj
    exact hj

  refine ⟨j.1, j.2.1, ?_⟩
  rw [lbIso_pull_iff hA hB, ← pullbackRestrictIsoRestrict_inv_fst, CechPic.pull_comp, CechPic.pull_comp, hj']

end GlobalTheory.StalkLBIso
