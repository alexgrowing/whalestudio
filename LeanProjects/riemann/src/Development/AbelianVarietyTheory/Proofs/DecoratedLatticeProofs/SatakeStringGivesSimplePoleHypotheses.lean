import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.StringPole

theorem good_of_not_mem_above {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    GlobalTheory.Hk3.Good R t w := by
  intro PP hPP
  have hmem : PP.under (𝓞 D.host.F) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
    exact Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hw hmem
  · intro hc
    have e := GlobalTheory.GoodPrimes.isConjPl_iff.1 hc
    apply hw
    show w.under (𝓞 D.host.F) ∈ (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))
    rw [e, GlobalTheory.TwistTypePlaces.under_conjPl]
    exact hmem

end GlobalTheory.Core.Rk.StringPole

open GlobalTheory.Core.Rk.StringPole in

theorem GlobalTheory.Core.Rk.StringPole.string_pole_hyp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t s, HasString R i t s → ∃ B c : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧ GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))) D.R.r D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i t s hs
  classical
  obtain ⟨B, hB, hstr⟩ := hs
  set x := GlobalTheory.LFun.val (F := D.host.F) (chiV R i t) with hx
  let c : GlobalTheory.LFun.Fam D.host.E := fun w => B w - GlobalTheory.LFun.segFam x D.R.t w
  refine ⟨B, c, hB, (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t).finite_toSet, D.R.rank_add_five_le, fun w hw => ?_⟩
  have hg := good_of_not_mem_above R t w hw
  obtain ⟨B', hB', hbd⟩ := hstr w hg
  have hcard : (B w).card = (Vc D i).rank := by
    rcases hB (w.under (𝓞 D.host.F)) (fun h => hw h) w rfl with ⟨_, h2, _⟩ | ⟨_, τ, ϖ, α, _, _, h3, _⟩
    · exact h2
    · rw [h3]
      simp [GlobalTheory.LGrp.bcParam]
      omega
  have hrank : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hseg : (GlobalTheory.LFun.segFam x D.R.t w).map (fun a : ℂˣ => (a : ℂ)) =
      str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t := by
    unfold GlobalTheory.LFun.segFam GlobalTheory.LFun.seg str
    rw [Multiset.map_map]
    rfl
  have hle : GlobalTheory.LFun.segFam x D.R.t w ≤ B w := by
    refine (Multiset.map_le_map_iff (f := fun a : ℂˣ => (a : ℂ)) Units.val_injective).1 ?_
    rw [hB', hseg]
    exact Multiset.le_add_left _ _
  have hsplit : B w = c w + GlobalTheory.LFun.segFam x D.R.t w := (tsub_add_cancel_of_le hle).symm
  have hc' : (c w).map (fun a : ℂˣ => (a : ℂ)) = B' := by
    have := congrArg (Multiset.map fun a : ℂˣ => (a : ℂ)) hsplit
    rw [Multiset.map_add, hB', hseg] at this
    exact (add_right_cancel this).symm
  refine ⟨?_, ?_, GlobalTheory.LFun.norm_val _ _, GlobalTheory.LFun.norm_val _ _, ?_⟩
  · have := congrArg Multiset.card hsplit
    rw [Multiset.card_add, hcard, hrank] at this
    simp only [GlobalTheory.LFun.segFam, GlobalTheory.LFun.card_seg] at this
    omega
  · intro b hb
    have hb' : (b : ℂ) ∈ B' := hc' ▸ Multiset.mem_map_of_mem _ hb
    exact hbd _ hb'
  · show B w = GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam c x x D.R.t w
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.liftFam
    rw [mul_inv_cancel, GlobalTheory.LFun.twist_one]
    exact hsplit
