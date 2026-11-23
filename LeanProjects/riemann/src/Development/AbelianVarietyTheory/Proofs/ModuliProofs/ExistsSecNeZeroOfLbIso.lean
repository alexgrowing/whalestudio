import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsCoverCubeEffectiveAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionNeZeroFibreOfGenericSectionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianSchemeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleSpecialisation

theorem exists_sec_ne_zero_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push Not at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pull_div_lbPow {X Y : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (a : ℕ) :
    LBIso ((LB.div (lbPow M a) L).pull f) (LB.div (lbPow (M.pull f) a) (L.pull f)) := by
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hp' : (lbPow (M.pull f) a).IsLB := LB.isLB_linComb (pull_isLB hM f) _ _
  refine (CechPic.cls_eq_iff (pull_isLB (LB.isLB_div hp hL) f) (LB.isLB_div hp' (pull_isLB hL f))).1 ?_
  rw [CechPic.cls_pull (LB.isLB_div hp hL), CechPic.cls_div hp hL, CechPic.cls_div hp' (pull_isLB hL f),
    CechPic.cls_lbPow hM, CechPic.cls_lbPow (pull_isLB hM f), CechPic.cls_pull hM, CechPic.cls_pull hL,
    map_sub, map_nsmul]

def baseChange {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) : Out.PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem relAmple_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (P : Out.PolAV S) (M : LB P.A.left) (K : Type) [Field K] (x : Sp K ⟶ S), M.IsLB → Set.range x = {genericPoint S} → Out.RelAmple ((Over.pullback x).obj P.A) (M.pull (pullback.fst P.A.hom x)) → Out.RelAmple P.A M := by
  intro hL _ S _ _ P M K _ x hM hx hamp
  have hne : Nonempty (baseChange P x).A.left :=
    ⟨eSec (baseChange P x).A (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero K (baseChange P x).A (baseChange P x).L (M.pull (pullback.fst P.A.hom x))
    (baseChange P x).isAb.proper hne (baseChange P x).isLB (pull_isLB hM _) hamp
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN := LB.isLB_div hp P.isLB
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ P.A.left), (LB.div (lbPow (M.pull f) a) (P.L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB P.isLB f)
  obtain ⟨t, ht⟩ := exists_sec_ne_zero_of_lbIso (pull_isLB hN _) (hN' _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom x) a) ⟨s, hs⟩
  refine GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme hL S P M hM fun K' _ _ y => ?_
  obtain ⟨t', ht'⟩ := exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom y) a).symm
    (GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section hL S P _ K K' x y t hN hx ht)
  obtain ⟨r, u, hu⟩ := GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety.1 K' (baseChange P y) _ t' (hN' _) ht'
  exact GlobalTheory.T.relAmple_of_cube_div_generated_field K' (baseChange P y).A (baseChange P y).L (M.pull (pullback.fst P.A.hom y)) a r u
    (baseChange P y).isAb.proper (baseChange P y).isLB (pull_isLB hM _) ha (baseChange P y).ample hu

end GlobalTheory.AmpleSpecialisation
