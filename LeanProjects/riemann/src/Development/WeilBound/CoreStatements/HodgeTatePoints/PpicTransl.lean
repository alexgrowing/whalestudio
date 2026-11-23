import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfFlatOfClosedPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.CechPic GlobalTheory.PrimitiveOverValuationRing

theorem isIso_transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A) := by
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩
  · rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit,
      inv_mul_cancel_left]
  · rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, mul_inv_cancel_left]

theorem cls_translDiff {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} (y : T ⟶ A)
    (h : (Out.translDiff A L y).IsLB) :
    cls _ h = GlobalTheory.CechPic.pull ((fst T A ≫ y) * snd T A).left (cls L hL) - GlobalTheory.CechPic.pull (snd T A).left (cls L hL) :=
  cls_pair hL _ _ h

theorem kTriv_transl {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) (x : 𝟙_ (Over S) ⟶ A) (h : LBIso M (L.pull ((toUnit A ≫ x) * 𝟙 A).left)) (hK : Out.KTriv A L) :
    Out.KTriv A M := by
  have hτ : ((toUnit A ≫ x)⁻¹ * 𝟙 A) ≫ ((toUnit A ≫ x) * 𝟙 A) = 𝟙 A := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, mul_inv_cancel_left]
  have hcM : cls M hM = GlobalTheory.CechPic.pull ((toUnit A ≫ x) * 𝟙 A).left (cls L hL) := by
    rw [(cls_eq_iff hM (LB.isLB_pull hL _)).mpr h, cls_pull hL]
  intro R _ t y hy
  apply hK R t y
  intro p
  obtain ⟨V, hpV, c, hc⟩ := hy p
  refine ⟨V, hpV, ?_⟩
  have hLy : (Out.translDiff A L y).IsLB := LB.isLB_linComb hL _ _
  have hMy : (Out.translDiff A M y).IsLB := LB.isLB_linComb hM _ _
  have hc0 := (cls_eq_zero_iff (LB.isLB_pull hMy _)).mpr ⟨c, hc⟩
  rw [cls_pull hMy, cls_translDiff hM, hcM, ← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp,
    ← Over.comp_left, ← Over.comp_left] at hc0
  have hm : (fst (Over.mk t) A ≫ y * snd (Over.mk t) A) ≫ ((toUnit A ≫ x) * 𝟙 A) =
      lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A)) ≫
        (fst (Over.mk t) A ≫ y * snd (Over.mk t) A) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, MonObj.comp_mul,
      ← Category.assoc, lift_fst, lift_snd, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      comp_toUnit, mul_left_comm]
  have hs : snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A) =
      lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A)) ≫ snd (Over.mk t) A :=
    (lift_snd _ _).symm
  rw [hs, hm, Over.comp_left, Over.comp_left, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_comp,
    ← map_sub] at hc0
  have hψφ : lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A)) ≫
      lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A)) = 𝟙 _ := by
    ext
    · rw [Category.assoc, lift_fst, lift_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, ← Category.assoc, lift_snd, Category.assoc, hτ, Category.comp_id,
        Category.id_comp]
  have hψf : (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A))).left ≫
      (fst (Over.mk t) A).left = (fst (Over.mk t) A).left := by
    rw [← Over.comp_left, lift_fst]
  have key := pull_eq_zero_of_mem _
    ((Over.Hom.left (fst (Over.mk t) A) ⁻¹ᵁ V).ι ≫
      (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A))).left)
    (fun z => by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Category.assoc, hψf, Scheme.Hom.comp_apply,
        ← Scheme.Hom.mem_preimage]
      exact (Scheme.Opens.range_ι _).le (Set.mem_range_self z)) hc0
  have e : ∀ D, GlobalTheory.CechPic.pull
      (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A))).left
      (GlobalTheory.CechPic.pull (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A))).left D) = D := by
    intro D
    rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, hψφ, Over.id_left, GlobalTheory.CechPic.pull_id]
  rw [GlobalTheory.CechPic.pull_comp, e] at key
  exact (cls_eq_zero_iff (LB.isLB_pull hLy _)).mp (by rw [cls_pull hLy, cls_translDiff hL]; exact key)

theorem transl : ∀ (Q : Out.PolAV (Sp ℂ)) (M : LB Q.A.left), M.IsLB → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, LBIso M (Q.L.pull ((toUnit Q.A ≫ x) * 𝟙 Q.A).left) → Out.RelAmple Q.A M ∧ Out.KTriv Q.A M := by
  intro Q M hM x h
  have := Q.isAb.comm
  refine ⟨?_, kTriv_transl Q.isLB hM x h Q.ktriv⟩
  obtain ⟨w, hw⟩ := h
  have := isIso_transl x
  have : IsIso ((toUnit Q.A ≫ x) * 𝟙 Q.A).left :=
    inferInstanceAs (IsIso ((Over.forget (Sp ℂ)).map ((toUnit Q.A ≫ x) * 𝟙 Q.A)))
  have sq : IsPullback ((toUnit Q.A ≫ x) * 𝟙 Q.A).left Q.A.hom Q.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  exact relAmple_pull sq Q.isLB hM ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample

end PositivityTheory.HtPt.Ppic
