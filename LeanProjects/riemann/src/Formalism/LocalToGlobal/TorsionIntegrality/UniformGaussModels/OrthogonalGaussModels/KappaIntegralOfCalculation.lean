import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

theorem kappa_integral_of_calculation (hC : CalcC) : uniformGaussModelConditionReformulated := by
  intro l _ hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN n _ _ Θ γ hγ hK
  obtain ⟨hFr, hF1, hall, hbin⟩ := hC l hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  have hσ : ∀ a : MaximalUnramifiedExtension l, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq (MaximalUnramifiedExtension l) l σ hU).2
  let _ : StarRing (BrC.Osub σ) := BrC.starO hσ
  have hun : (Matrix.of fun a b => (⟨γ a b, BrC.mem_Osub.2 (hγ.1 a b)⟩ : BrC.Osub σ)).conjTranspose *
      (Matrix.of fun a b => (⟨γ a b, BrC.mem_Osub.2 (hγ.1 a b)⟩ : BrC.Osub σ)) = 1 := by
    ext a b
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, Matrix.one_apply]
    have h := hγ.2 a b
    have e : ((if a = b then (1 : BrC.Osub σ) else 0 : BrC.Osub σ) : MaximalUnramifiedExtension l) =
        if a = b then 1 else 0 := by split_ifs <;> rfl
    rw [e, ← h]
    rfl
  exact Formalism.L2.Th1.E.generalIntOf ℂ_[l] (unitBall ℂ_[l]) (fun _ => Iff.rfl)
    (lgF ℂ_[l] l) (expF ℂ_[l] l) (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) hFr
    (BrC.Osub σ) ((MaximalUnramifiedExtension l).subtype.comp (BrC.Osub σ).subtype)
    (fun α => (hall α.1 α.2.1 α.2.2).1)
    (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz))
    hF1
    (fun α => (hall α.1 α.2.1 α.2.2).2.1)
    (fun α => (hall α.1 α.2.1 α.2.2).2.2)
    n Θ (Matrix.of fun a b => (⟨γ a b, BrC.mem_Osub.2 (hγ.1 a b)⟩ : BrC.Osub σ)) hun hK

theorem HypShape_of (hC : CalcC) : HypShape := by
  intro l _ hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN N0 N1 ιr _ _ n _ f f' hff Θ hΘ
  have hl2 : 2 ≤ l := by omega
  obtain ⟨hFr, hF1, hall, hbin⟩ := hC l hl g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  obtain ⟨hf, hf', hG1, hG2, hG3⟩ := hff
  have hσ : ∀ a : MaximalUnramifiedExtension l, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq (MaximalUnramifiedExtension l) l σ hU).2
  let _ : StarRing (BrC.Osub σ) := BrC.starO hσ
  have gram : ∀ (a b : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l)
      (ha : ∀ e i, ‖a e i‖ ≤ 1 ∧ σ (σ (a e i)) = a e i) (hb : ∀ e i, ‖b e i‖ ≤ 1 ∧ σ (σ (b e i)) = b e i)
      (e e' : ιr × Fin N0 × Fin N1) (c : BrC.Osub σ), ∑ i, σ (a e i) * b e' i = c.1 →
      ∑ i, star (⟨a e i, BrC.mem_Osub.2 (ha e i)⟩ : BrC.Osub σ) *
        (⟨b e' i, BrC.mem_Osub.2 (hb e' i)⟩ : BrC.Osub σ) = c := by
    intro a b ha hb e e' c h
    apply Subtype.ext
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    rfl
  have hph : PowerSeries.constantCoeff (phL l g2 g3 s2 ε) = 0 := hFr.2.2
  have hPh0 : MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph
  have hpt : ∀ i, Formalism.L2.Th1.C.IsPt (unitBall ℂ_[l])
      (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f' i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hFr.1 hFr.2.1
      (by
        rintro (e | e)
        · exact (hall _ (hf e i).1 (hf e i).2).1
        · exact (hall _ (hf' e i).1 (hf' e i).2).1)
      (by rintro (e | e) <;> exact Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X _)
  obtain ⟨h3, h4, h5⟩ := Formalism.L2.Th1.E.substExpInt ℂ_[l] n (Bool × ιr × Fin N0 × Fin N1)
    (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f') (fun i => (hpt i).1)
    (fun i => (hpt i).2) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) _ hPh0 hΘ
  have hΘe : Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ) := by
    rw [← mul_assoc]
    have := Formalism.L2.Th1.C.mvExp_neg hPh0
    rw [← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq] at this
    rw [this, one_mul]
  refine ⟨_, _, h4, h5, ?_, ?_⟩
  · have hF0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF.1, map_zero]
    have hcob : cob (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) (lgF ℂ_[l] l) = 0 := by
      rw [← Formalism.L2.Th1.E.Joints.map_lgF' (MaximalUnramifiedExtension l).subtype l, ← Formalism.L2.Th1.E.mapCob _ _ _ _ _ hF.1,
        hF.2.2, map_zero]
    rw [Formalism.L2.Th1.E.mapCob _ _ _ _ _ hF.1,
      Formalism.L2.Th1.E.sumEBridge ℂ_[l] (lgF ℂ_[l] l) (expF ℂ_[l] l) (BrC.logPair hl2) _ hF0 hcob]
    refine (Formalism.L2.Th1.E.congIffSimeq ℂ_[l] (unitBall ℂ_[l]) (fun _ => Iff.rfl) _ _ _).1 ?_
    rw [Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ fun i => (hpt i).1]
    exact Formalism.L2.Th1.C.hyperbolicSum ℂ_[l] (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) hFr
      (BrC.Osub σ) ((MaximalUnramifiedExtension l).subtype.comp (BrC.Osub σ).subtype)
      (fun α => (hall α.1 α.2.1 α.2.2).1)
      (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz))
      hF1
      (fun α => (hall α.1 α.2.1 α.2.2).2.1)
      (fun α => (hall α.1 α.2.1 α.2.2).2.2)
      n (ιr × Fin N0 × Fin N1)
      (fun e i => ⟨f e i, BrC.mem_Osub.2 (hf e i)⟩) (fun e i => ⟨f' e i, BrC.mem_Osub.2 (hf' e i)⟩)
      (fun e e' => gram f f hf hf e e' 0 (hG1 e e'))
      (fun e e' => gram f' f' hf' hf' e e' 0 (hG2 e e'))
      (fun e e' => gram f f' hf hf' e e' _ (by
        rw [hG3 e e']
        split_ifs <;> rfl))
      (Bool × ιr × Fin N0 × Fin N1)
      (fun e => MvPowerSeries.X (false, e)) (fun e => MvPowerSeries.X (true, e))
      (fun e => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X _) (fun e => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X _)
  · unfold inHyp
    rw [← h3, ← hΘe]

end Formalism.L2.Th1.Top
