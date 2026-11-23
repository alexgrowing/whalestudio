import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDualStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.BlowAmple
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.ProjBlowup

theorem ample_twist_of_blowup : ∀ (K : Type) [Field K] [NumberField K] (X X' N : Scheme.{0}) (s : X ⟶ Sp (𝓞 K)) (J : X.IdealSheafData)
    (b : X' ⟶ X) (ν : N ⟶ X') (EX : GlobalTheory.EffCartierData N), IsProjOver s → FinalTheorems.Blowup b J → IsFinite ν →
    EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, GlobalTheory.IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (GlobalTheory.CechPic.dual EX.lb)) := by
  intro K _ _ X X' N s J b ν EX hs hb hν hEX L hL
  obtain ⟨L₀, m, σ, hL₀, hσ⟩ := GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf (𝓞 K) X s J hs
  obtain ⟨c, hc, hprop, hci⟩ := GlobalTheory.T.exists_closedImmersion_blowup_generatingSections (𝓞 K) X X' s J b L₀ m σ hs hb hσ
  have hψ : Proportional σ (ν ≫ b) (ν ≫ c) := hprop.comp ν
  have hiso := GlobalTheory.T.pullback_O1_iso_blowup_twist_dual (𝓞 K) X N J L₀ m σ (ν ≫ b) (ν ≫ c) EX hL₀ hσ hψ hEX
  have : IsProper s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str (𝓞 K) n
    infer_instance
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (GlobalTheory.AmpleDominates.eventually_isAmpleLB s hL hL₀)
  refine ⟨T₀, fun T hT => ?_⟩
  have hA := hT₀ T hT
  have hO := isAmple_projective_O_one (𝓞 K) m
  set A := LB.div (lbPow L T) L₀ with hAdef
  set p := pullback.fst s (PSpace.str (𝓞 K) m)
  set q := pullback.snd s (PSpace.str (𝓞 K) m)
  set B := tens (A.pull p) ((O1 (𝓞 K) m).pull q)
  have hBL : B.IsLB := isLB_tens (LB.isLB_pull hA.isLB _) (LB.isLB_pull hO.isLB _)
  have hB : IsAmpleLB B := by
    refine hA.box hO hBL (IsPullback.of_hasPullback s (PSpace.str (𝓞 K) m)) ?_
    have h1 := LB.isLB_div hBL (LB.isLB_pull hA.isLB p)
    refine (cls_eq_zero_iff (LB.isLB_div h1 (LB.isLB_pull hO.isLB q))).1 ?_
    rw [cls_div h1 (LB.isLB_pull hO.isLB q), cls_div hBL (LB.isLB_pull hA.isLB p),
      cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q)]
    abel
  let h : N ⟶ pullback s (PSpace.str (𝓞 K) m) := ν ≫ pullback.lift b c hc
  have hp : h ≫ p = ν ≫ b := by
    simp only [h, p, Category.assoc]; rw [pullback.lift_fst]
  have hq : h ≫ q = ν ≫ c := by
    simp only [h, q, Category.assoc]; rw [pullback.lift_snd]
  have h2 := hB.pull_of_isAffineHom h
  have hT : (GlobalTheory.CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (GlobalTheory.CechPic.dual EX.lb)).IsLB :=
    isLB_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb)
  refine h2.of_lbIso hT ((cls_eq_iff hT (LB.isLB_pull hBL h)).1 ?_)
  have hG := (cls_eq_iff (LB.isLB_pull hO.isLB _) (isLB_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb))).2 hiso
  rw [cls_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb, cls_pull hO.isLB, cls_pull hL₀] at hG
  rw [cls_pull hBL, cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q), cls_pull hA.isLB, cls_pull hO.isLB,
    cls_div (isLB_lbPow hL.isLB T) hL₀, cls_lbPow hL.isLB,
    cls_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb,
    cls_lbPow (LB.isLB_pull hL.isLB _), cls_pull hL.isLB, map_add, ← pull_comp, ← pull_comp, hp, hq, hG]
  simp only [map_sub, map_nsmul]
  abel

end GlobalTheory.BlowAmple
