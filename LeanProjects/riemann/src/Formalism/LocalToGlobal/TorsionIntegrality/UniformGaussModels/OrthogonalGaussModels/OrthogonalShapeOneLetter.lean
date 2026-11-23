import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

namespace ConjugatePartitionShape

theorem factors (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 ε s2 : MaximalUnramifiedExtension l) (h2 : (g2 : ℂ_[l]) = ι L.g₂) (h3 : (g3 : ℂ_[l]) = ι L.g₃)
    (hs2 : (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L)) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1)
    (hD : ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1) (hε : ‖ε‖ = 1)
    (hθ : ∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1)
    (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) (hω2 : ω₀ / 2 ∉ L.lattice)
    (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N) (s : ℂ) (hs : (N : ℂ) * s ∈ L.lattice) :
    ∃ V : PowerSeries ℂ_[l], Formalism.L2.Th1.E.IntS V ∧
      (Formalism.DworkPowerSeriesWeights.mvExp (-(PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε))) : PowerSeries ℂ_[l]) * V =
        thetaOne l L ι (ε : ℂ_[l]) ω₀ s := by
  have hW : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL l L ι) := by
    unfold Formalism.L2.Th1.E.curveL
    rw [← h2, ← h3]
    exact Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short l hl _ _ hg2 hg3 hD
  exact Formalism.L2.Th1.E.joint_integrality l L ι (by omega) hW g2 g3 s2 ε h2 h3 hs2 hε hθ ω₀ hω hω2 s N hN hlN hs

theorem cc_ph (l : ℕ) [Fact l.Prime] (hl : 2 ≤ l) (g2 g3 s2 ε : MaximalUnramifiedExtension l) :
    PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF hl, map_zero]

end ConjugatePartitionShape

open ConjugatePartitionShape

theorem orthogonal_shape_one_letter : OrthShapeOne := by
  intro l _ hl L ι g2 g3 ε s2 h2 h3 hs2 hg2 hg3 hD hε hθ n _ ω₀ hω hω2 κ _ r s N hr hN hlN hs
  choose V hV hVe using fun k i =>
    factors l hl L ι g2 g3 ε s2 h2 h3 hs2 hg2 hg3 hD hε hθ ω₀ hω hω2 N hN hlN (s k i) (hs k i)
  obtain ⟨e, hI⟩ := Formalism.L2.Th1.E.prodInt ℂ_[l] κ n
    (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) r V (cc_ph l (by omega) g2 g3 s2 ε) hr hV
  refine ⟨_, hI, ?_⟩
  simp only [hVe] at e
  exact e

theorem OrthShape_of (hC : CalcC) : OrthShape := by
  intro l _ hl L ι g2 g3 ε s2 h2 h3 hs2 hg2 hg3 hD hε hθ σ hU F hF hN N0 N1 ιr _ _ n _ f f' hff
    ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  have hl2 : 2 ≤ l := by omega
  choose V hV hVe using fun k i =>
    factors l hl L ι g2 g3 ε s2 h2 h3 hs2 hg2 hg3 hD hε hθ ω₀ hω hω2 N hN0 hlN (s k i) (hs k i)
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
  obtain ⟨U0, Φ, hU0, hΦ0, hΦ, hE⟩ := Formalism.L2.Th1.E.intHyp ℂ_[l] (unitBall ℂ_[l]) (fun _ => Iff.rfl)
    (lgF ℂ_[l] l) (expF ℂ_[l] l) (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) hFr
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
    κ r V hr hV
  refine ⟨U0, Φ, hU0, hΦ0, ?_, ?_⟩
  · have hF0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF.1, map_zero]
    have hcob : cob (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F) (lgF ℂ_[l] l) = 0 := by
      rw [← Formalism.L2.Th1.E.Joints.map_lgF' (MaximalUnramifiedExtension l).subtype l, ← Formalism.L2.Th1.E.mapCob _ _ _ _ _ hF.1,
        hF.2.2, map_zero]
    rw [Formalism.L2.Th1.E.mapCob _ _ _ _ _ hF.1,
      Formalism.L2.Th1.E.sumEBridge ℂ_[l] (lgF ℂ_[l] l) (expF ℂ_[l] l) (BrC.logPair hl2) _ hF0 hcob]
    exact hΦ
  · simp only [hVe] at hE
    exact hE

end Formalism.L2.Th1.Top
