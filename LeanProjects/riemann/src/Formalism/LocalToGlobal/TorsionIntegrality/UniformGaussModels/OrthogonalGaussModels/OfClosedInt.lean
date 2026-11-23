import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

theorem PhMap_proof : PhMap := fun _ _ _ _ _ _ φ _ hl g2 g3 s2 ε =>
  Formalism.L2.Th1.E.Joints.map_phFF φ hl g2 g3 s2 ε

namespace PAdicPowerSeriesCoefficients

section Maps

variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (φ : K →+* K')

theorem cc_map {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.constantCoeff (PowerSeries.map φ f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero]

theorem map_expF {l : ℕ} (hl : 2 ≤ l) : PowerSeries.map φ (expF K l) = expF K' l := by
  refine (expSpec K' l hl).2.2.2 _ (cc_map φ (expSpec K l hl).1) ?_
  rw [← Formalism.L2.Th1.E.Joints.map_lgF' φ l, ← Formalism.L2.Th1.B.Map.map_psubst' φ (expSpec K l hl).1,
    (expSpec K l hl).2.1, PowerSeries.map_X]

theorem map_mulBy {l : ℕ} (hl : 2 ≤ l) (a : K) :
    PowerSeries.map φ (Formalism.L2.Th1.C.mulBy (lgF K l) (expF K l) a) =
      Formalism.L2.Th1.C.mulBy (lgF K' l) (expF K' l) (φ a) := by
  unfold Formalism.L2.Th1.C.mulBy
  rw [Formalism.L2.Th1.B.Map.map_psubst' φ (FAux.cc_arg hl a), map_mul, PowerSeries.map_C,
    Formalism.L2.Th1.E.Joints.map_lgF', map_expF φ hl]

theorem cc_mulBy {l : ℕ} (hl : 2 ≤ l) (a : K) :
    PowerSeries.constantCoeff (Formalism.L2.Th1.C.mulBy (lgF K l) (expF K l) a) = 0 :=
  Pair.cc_ps (τ := Unit) (FAux.cc_arg hl a) (expSpec K l hl).1

end Maps

section Field

variable {l : ℕ} [Fact l.Prime]

theorem lg_map {τ : Type} {f : MvPowerSeries τ (MaximalUnramifiedExtension l)}
    (h : Formalism.L2.Th1.C.LG (unitBall (MaximalUnramifiedExtension l)) f) :
    Formalism.L2.Th1.C.LG (unitBall ℂ_[l]) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype f) := by
  refine ⟨?_, fun n => ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.1, map_zero]
  · unfold Formalism.L2.Th1.C.mvExp
    rw [← PowerSeries.map_exp (MaximalUnramifiedExtension l).subtype, ← Formalism.L2.Th1.B.Map.map_psubst (MaximalUnramifiedExtension l).subtype h.1,
      MvPowerSeries.coeff_map]
    exact h.2 n

theorem of_closed_int {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hU : UnrOK (MaximalUnramifiedExtension l) l σ) {P : ℂ_[l] → Prop}
    (hc : IsClosed {z : ℂ_[l] | P z}) (hi : ∀ n : ℤ, P (n : ℂ_[l])) {x : MaximalUnramifiedExtension l} (hx : ‖x‖ ≤ 1)
    (hs : σ x = x) : P (x : ℂ_[l]) :=
  BrC.of_closed_int hU (P := fun z : MaximalUnramifiedExtension l => P (z : ℂ_[l])) (hc.preimage continuous_subtype_val)
    (fun n => by simpa using hi n) hx hs

theorem endInt {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hU : UnrOK (MaximalUnramifiedExtension l) l σ) {α : MaximalUnramifiedExtension l} (hα : ‖α‖ ≤ 1)
    (hs : σ (σ α) = α) :
    Formalism.L2.Th1.C.EndInt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]) := by
  intro n
  have h := map_mulBy (MaximalUnramifiedExtension l).subtype hU.1.two_le α
  rw [show (α : ℂ_[l]) = (MaximalUnramifiedExtension l).subtype α from rfl, ← h, PowerSeries.coeff_map]
  exact BrC.endInt hU hα hs n

theorem phNorm {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hl : 2 ≤ l) {ph : PowerSeries (MaximalUnramifiedExtension l)} {α : MaximalUnramifiedExtension l}
    (h : NormRel l σ ph α) :
    Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype ph) (α : ℂ_[l]) ((σ α : MaximalUnramifiedExtension l) : ℂ_[l]) := by
  have h1 := lg_map ((BrC.phNorm_iff ph α).2 h)
  unfold Formalism.L2.Th1.C.PhNormAt Formalism.L2.Th1.C.Cong
  have e : MvPowerSeries.map (MaximalUnramifiedExtension l).subtype
      (PowerSeries.subst (Formalism.L2.Th1.C.mulBy (lgF (MaximalUnramifiedExtension l) l) (expF (MaximalUnramifiedExtension l) l) α) ph -
        (α * σ α) • ph) =
      PowerSeries.subst (Formalism.L2.Th1.C.mulBy (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]))
        (PowerSeries.map (MaximalUnramifiedExtension l).subtype ph) -
        ((α : ℂ_[l]) * ((σ α : MaximalUnramifiedExtension l) : ℂ_[l])) • PowerSeries.map (MaximalUnramifiedExtension l).subtype ph := by
    rw [map_sub, Formalism.L2.Th1.B.Map.map_psubst (MaximalUnramifiedExtension l).subtype (cc_mulBy hl α),
      MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C]
    have h2 : MvPowerSeries.map (MaximalUnramifiedExtension l).subtype
        (Formalism.L2.Th1.C.mulBy (lgF (MaximalUnramifiedExtension l) l) (expF (MaximalUnramifiedExtension l) l) α) =
        Formalism.L2.Th1.C.mulBy (lgF ℂ_[l] l) (expF ℂ_[l] l) (α : ℂ_[l]) :=
      map_mulBy (MaximalUnramifiedExtension l).subtype hl α
    rw [h2, map_mul]
    rfl
  rw [← e]
  exact h1

end Field

end PAdicPowerSeriesCoefficients

open PAdicPowerSeriesCoefficients in
theorem CalcC_proof : CalcC := by
  intro l _ h5 g2 g3 ε s2 hg2 hg3 hε hth σ hU F _ hN
  have hl : 2 ≤ l := hU.1.two_le
  have hnl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h : ‖(((l : ℕ) : MaximalUnramifiedExtension l) : ℂ_[l])‖ = (l : ℝ)⁻¹ := hU.2.2.1
    simpa using h
  have hP := BrC.logPair (K := ℂ_[l]) hl
  obtain ⟨F', hF'⟩ := (Formalism.InvariantFactorPaths.G7.Top.lawExists ℂ_[l] l hU.1 hnl).1
  have hph : PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) = 0 :=
    cc_map _ (FAux.cc_phFF hl g2 g3 s2 ε)
  have hth' : ∀ n, ‖PowerSeries.coeff n (thetaS l (g2 : ℂ_[l]) (g3 : ℂ_[l]) (ε : ℂ_[l]))‖ ≤ 1 := by
    intro n
    have hm := FAux.thetaS_map (MaximalUnramifiedExtension l).subtype hl g2 g3 ε
    have e : thetaS l (g2 : ℂ_[l]) (g3 : ℂ_[l]) (ε : ℂ_[l]) =
        PowerSeries.map (MaximalUnramifiedExtension l).subtype (thetaS l g2 g3 ε) := hm.symm
    rw [e, PowerSeries.coeff_map]
    exact hth n
  have hF1 : F1 F' (cob F' (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε))) := by
    rw [PhMap_proof _ _ (MaximalUnramifiedExtension l).subtype l hl]
    exact first_level_on_curve ℂ_[l] l hU.1 hU.2.1 hnl F' hF' _ _ _ _ hg2 hg3 hε hth'
  obtain ⟨-, hFG, hC1⟩ := Formalism.L2.Th1.C.first_level_from_universal_holds ℂ_[l] F' _ _ _ hP (BrC.lawLog hl hF')
    hph hF1.2.1
  have hFr : Formalism.L2.Th1.C.Frame (unitBall ℂ_[l]) (lgF ℂ_[l] l) (expF ℂ_[l] l)
      (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) := ⟨hP, hFG, hph⟩
  have hσ : ∀ a : MaximalUnramifiedExtension l, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (frobSq (MaximalUnramifiedExtension l) l σ hU).2
  have hcl := Formalism.L2.Th1.C.unit_ball_closed ℂ_[l]
  have hbin : ∀ z : MaximalUnramifiedExtension l, ‖z‖ ≤ 1 → σ z = z →
      Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[l]) (z : ℂ_[l]) := fun z hz hs =>
    of_closed_int hU (Formalism.L2.Th1.C.binomClosed ℂ_[l] _ hcl) (Formalism.L2.Th1.C.intBinomScalar ℂ_[l] _)
      hz hs
  let _ : StarRing (BrC.Osub σ) := BrC.starO hσ
  have key := Formalism.L2.Th1.C.normAdjAll ℂ_[l] (unitBall ℂ_[l]) _ _ _ hFr (BrC.Osub σ)
    ((MaximalUnramifiedExtension l).subtype.comp (BrC.Osub σ).subtype)
    (fun α => endInt hU α.2.1 α.2.2)
    (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz))
    (fun z hz => of_closed_int hU
      (Formalism.L2.Th1.C.zLinClosed ℂ_[l] _ hcl _ _ _ hP.1 hP.2.2.1 hph)
      (Formalism.L2.Th1.C.zLinInt ℂ_[l] _ _ _ _ hFr hC1) z.2.1 (congrArg Subtype.val hz))
    hC1
    (by
      show ‖(2 : ℂ_[l])⁻¹‖ ≤ 1
      have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := BrC.norm_two hU
      have h3 : ‖(2 : ℂ_[l])‖ = 1 := by rw [← h2, ← FAux.norm_coe, map_ofNat]
      rw [norm_inv, h3, inv_one])
    (by
      have : (2 : BrC.Osub σ) =
          (BrC.unitO (BrC.norm_two hU) (by rw [map_ofNat, map_ofNat]) : (BrC.Osub σ)ˣ) :=
        Subtype.ext rfl
      rw [this]
      exact Units.isUnit _)
    (BrC.two_units hU)
    (fun u => phNorm hl (hN _ (BrC.norm_unitO u) (u : BrC.Osub σ).2.2))
  refine ⟨hFr, hC1, fun α hα hs => ⟨endInt hU hα hs, ?_⟩, hbin⟩
  exact key ⟨α, BrC.mem_Osub.2 ⟨hα, hs⟩⟩

end Formalism.L2.Th1.Top
