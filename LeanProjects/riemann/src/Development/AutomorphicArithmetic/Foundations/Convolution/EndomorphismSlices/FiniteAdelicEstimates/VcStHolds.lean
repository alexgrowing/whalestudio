import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchFinal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.LefschetzHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.TrMulComm

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem vcSt_holds : VCSt :=
  VC.vcOf wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.2.2.2 GlobalTheory.CompanionTheory.GelC.gelComm GlobalTheory.CompanionTheory.GelFlagPf.gelFlag_holds
    GlobalTheory.CompanionTheory.FlagHerm.flagField_holds GlobalTheory.CompanionTheory.NilUnimod.nilUni GlobalTheory.CompanionTheory.KerZeroPf.main

private theorem lSt_holds : LSt :=
  LfSt.lOf_of_kChain LfSt.kChain_holds wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.2.2.1 wave_existence_speed_multiplicity.2.2.2
    (LfSt.chainOf'_holds wave_existence_speed_multiplicity.1 wave_existence_speed_multiplicity.2.1 GlobalTheory.CompanionTheory.GelC.gelComm GlobalTheory.CompanionTheory.KerZeroPf.main)
    GlobalTheory.CompanionTheory.ConeHaar.coneSt GlobalTheory.CompanionTheory.SuperHomot.homot GlobalTheory.CompanionTheory.SuppBound.suppSt

abbrev LefConcl {n : ℕ} (lam : Fin n → ℤ) (M : KMod n) (Tθ : M.V →L[ℂ] M.V) : Prop :=
  (∀ k, Tθ * M.ρ k = M.ρ k * Tθ) ∧ (∀ v, ‖Tθ v‖ = ‖v‖) ∧ Tθ * Tθ = 1 ∧
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (k : Mat n → (M.V →L[ℂ] M.V))
      (val : Inf n → ℂ) (T : ℝ), IsMult μ M k val T →
      (∀ (d : G n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ →
        (fun v => d.val *ᵥ v) '' perp W₂ = W₁ → (fun v => d.val *ᵥ v) '' perp W₁ = W₂ →
        ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure],
          ∫ u : N, phiOf M Tθ k (u * d) ∂ν = 0) ∧
      ∀ (d : G n) (z : Fin n → ℂ), d.val = diagonal z → (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
        Integrable (fun x => phiOf M Tθ k (PositivityTheory.RgTw.tw x d)) μ ∧
          ∫ x, phiOf M Tθ k (PositivityTheory.RgTw.tw x d) ∂μ =
            val (infOf lam) * starRingEnd ℂ (weylChar lam fun a => z a ^ 2)

theorem lefModel (n : ℕ) (lam : Fin n → ℤ) (hlam : Antitone lam) : LefConcl lam (lefE n lam) (lefT n lam) := by
  have h := cxData_model lam hlam
  exact ⟨h.TK, h.Tiso, h.Tsq, fun μ _ k val τ hk =>
    ⟨vcSt_holds n lam _ _ _ _ _ _ _ h μ k val τ hk, lSt_holds n lam _ _ _ _ _ _ _ h μ k val τ hk⟩⟩

theorem lefL : LefL := by
  intro E _ _ _ a b l₁ l₂ D A
  have LA := fun v : InfinitePlace E => lefModel a (l₁ v).w (l₁ v).anti
  have LB := fun v : InfinitePlace E => lefModel b (l₂ v).w (l₂ v).anti
  haveI := A.ha
  haveI := A.hb
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  refine ⟨⟨fun v k val T hm => vcBridge a A.μa (Ml l₁ v) (Tl l₁ v) k val T (LA v).1 hm ((LA v).2.2.2 A.μa k val T hm).1,
    fun v k val T hm => vcBridge b A.μb (Ml l₂ v) (Tl l₂ v) k val T (LB v).1 hm ((LB v).2.2.2 A.μb k val T hm).1⟩, ?_⟩
  intro v k k' val val' T hm hm'
  exact lefschetz_pair_holds a b A.μa A.μb (l₁ v) (l₂ v) _ _ _ _
    ⟨(F0.phiOf_cs A.μa (Ml l₁ v) (Tl l₁ v) k val T hm).1, (F0.phiOf_cs A.μa (Ml l₁ v) (Tl l₁ v) k val T hm).2,
      fun d z hd hz hi => ((LA v).2.2.2 A.μa k val T hm).2 d z hd hz hi |>.2⟩
    ⟨(F0.phiOf_cs A.μb (Ml l₂ v) (Tl l₂ v) k' val' T hm').1, (F0.phiOf_cs A.μb (Ml l₂ v) (Tl l₂ v) k' val' T hm').2,
      fun d z hd hz hi => ((LB v).2.2.2 A.μb k' val' T hm').2 d z hd hz hi |>.2⟩

end UpperTheory.Zero.ConvolutionTheory.EB

end
