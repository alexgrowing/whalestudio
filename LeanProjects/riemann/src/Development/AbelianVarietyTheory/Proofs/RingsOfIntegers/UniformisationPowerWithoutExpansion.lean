import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvenAlong
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SquareRes
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GmCharPow
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsoOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxIso
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymBox
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullGenBoxGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

section Level

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

omit [IsDomain R] [IsCommMonObj G] [IsCommMonObj G'] in
theorem rho_fst (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := pullback.lift_fst _ _ _

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem thickMap_rho (pG : IsPowGrp G' G j) (e : ℕ) (i : Fin j) :
    thickMap R I e G' ≫ rhoE I pG (e + 1) i = rhoE I pG e i ≫ thickMap R I e G := by
  have : Mono (fGl I G (e + 1)) := mono_fstG I (e + 1) G
  have a : thickMap R I e G ≫ fGl I G (e + 1) = fGl I G e := thickMap_fstG I e G
  have a' : thickMap R I e G' ≫ fGl I G' (e + 1) = fGl I G' e := thickMap_fstG I e G'
  rw [← cancel_mono (fGl I G (e + 1)), Category.assoc, Category.assoc, rho_fst, a, rho_fst, ← Category.assoc, a']

theorem thickMap_pG (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G) (e : ℕ)
    (g₀ : GtCoord I D'.toPre e G') (g₁ : GtCoord I D'.toPre (e + 1) G')
    (h₀ : ∀ i, g₀.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (h₁ : ∀ i, g₁.pG.left ≫ (pD.pw.pr i).left = rhoE I pG (e + 1) i ≫ (U.gt (e + 1)).pG.left) :
    thickMap R I e G' ≫ g₁.pG.left = g₀.pG.left := by
  have h : LevelCompat.thickMapOver I e G' ≫ g₁.pG = g₀.pG := pD.pw.lim.hom_ext fun ⟨i⟩ =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e G' ≫ ·) (h₁ i)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U.gt (e + 1)).pG.left) (thickMap_rho pG e i)).trans
        ((Category.assoc _ _ _).trans ((congrArg (rhoE I pG e i ≫ ·) (U.gt_q e)).trans (h₀ i).symm))))))
  exact congrArg (fun z => z.left) h

variable (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
include hq Q

theorem rig_level : RigAlong (T := (thickObj R I e G').left) w' (eSec (thickObj R I e G')) (thick R I e)
    (boxRig pG U.LG.L U.LG.rig) D'.toPre.rig := by
  obtain ⟨b, b₁, b₂⟩ := pD.w_rig
  exact rig_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq U.LG.rigGen (U.w_rig e)
    (fun i => by
      have := pG.hom i
      exact BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (pG.pr i)))
    (eSec_fstG I e G) (eSec_pG I (U.gt e)) (eSec_pG I g')
    (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) b b₁ b₂

theorem even_level (hG : GlobalFnsSt) : EvenAlong (T := (thickObj R I e G').left) w' (ι[thickObj R I e G']).left
    (boxSym pG U.LG.L U.symG) D'.toPre.sym := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  exact even_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q (rho_fst pG e) hq
    (fun i => by
      have := pG.hom i
      exact EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (pG.pr i)))
    (EvenPull.inv_fst _ G) (EvenPull.inv_hom_fst _ _ (U.gt e).q) (EvenPull.inv_hom_fst _ _ g'.q) (inv_pr pG)
    U.symG U.symG_gen D.toPre.sym D'.toPre.sym
    (fun y J J' hJ hJ' => PsiEvenBox.sym_box hG pD g'.pG.left y hJ hJ') (U.w_even e)

end Level

open GlobalTheory.WCub in
set_option maxHeartbeats 1600000 in

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ (U' : UnifPre I D' A' G') (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) := by
  intro hG R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  obtain ⟨gen, gen_hom, gen_pr, ext⟩ := exists_gen_pow R I j D D' A A' G G' pD pA pG U
  choose gt q_pr t_pr using fun e => GlobalTheory.PowTorusCoord.main hG R I j D D' A A' G G' pD pA pG e (U.gt e)
  have hq : ∀ e i, (gt e).pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left :=
    fun e i => (t_pr e 0).choose i 2
  choose w w_gen Q using fun e => PowerThickIso.main R I j D D' A A' G G' pD pA pG e (U.gt e) (gt e) (hq e)
    U.LG.L U.LG.isLB (U.w e) (U.w_gen e)
  have hL := boxIsLB _ G' G j pG U.LG.L U.LG.isLB
  have hr := boxRigIsGen _ G' G j pG U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen
  obtain ⟨c, hc⟩ := boxCubical _ G' G j pG U.LG U.cubG hL hr
  obtain ⟨s₁, s₂⟩ := boxSym_isSymmetry _ G' G j pG U.LG.L U.symG U.LG.isLB U.symG_gen U.symG_rig
  have gq := fun e => thickMap_pG pD pG U e (gt e) (gt (e + 1)) (hq e) (hq (e + 1))
  refine ⟨{
      smooth := (PowGrp.powers _ G' G j pG).1 U.smooth
      separated := (PowGrp.powers _ G' G j pG).2.1 U.separated
      gen := gen
      gen_hom := gen_hom
      LG := ⟨boxLB U.LG.L pG.pr, boxRig pG U.LG.L U.LG.rig, hL, hr⟩
      cubG := c
      symG := boxSym pG U.LG.L U.symG
      symG_gen := s₁
      symG_rig := s₂
      ext := ext
      gt := gt
      gt_q := gq
      gt_t := fun e χ => corr_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB D'.toPre.P.isLB pD.w (thickMap_rho pG e) (t_pr e χ).choose
        (t_pr (e + 1) χ).choose (LevelCompat.thickMap_Oφ (gt e) (gt (e + 1)) (gq e) χ) (t_pr e χ).choose_spec
        (t_pr (e + 1) χ).choose_spec (fun i => U.gt_t e _)
      w := w
      w_gen := w_gen
      w_rig := fun e => rig_level pD pG U e (gt e) (hq e) (w e) (Q e)
      w_even := fun e => even_level pD pG U e (gt e) (hq e) (w e) (Q e) hG
      w_cub := fun e T x jL jM _ cM => (clause_iff (tri (thick R I e) (gt e).pG x) (tri (thick R I e) (fstG I e G') x)
        (fun k : thK => (psum (thickObj R I e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM) (c.t.s jL)
        (fun k => (w e).s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hL _ => by
          rw [hc]
          exact cub_box hG pD pG U e (gt e) (hq e) (w e) (Q e) T x jL jM cM y hB hL
      w_compat := fun e => compat_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left)
        (T₁ := (thickObj R I (e + 1) G).left) (T₁' := (thickObj R I (e + 1) G').left)
        D.toPre.P.isLB (Q e) (Q (e + 1)) (U.w_compat e) (UnifPullRig.thickMap_fstG I e G) (U.gt_q e)
        (UnifPullRig.thickMap_fstG I e G') (gq e) (rho_fst pG e) (hq e) (thickMap_rho pG e) },
    Geo.Tor.idIso _, gen_pr, Geo.Tor.idIso_isGen hL, ?_, q_pr, t_pr, fun e jNM jM' jL' jNL => ?_⟩
  · exact idIso_rig U.LG.isLB U.LG.rig (fun i _ => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).e_comm) hr
  · exact square_res (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D'.toPre.P.isLB (w_gen e) (Q e)
      jNM jM' jL' jNL _ _ _ _ _

end GlobalTheory.PowUnif
