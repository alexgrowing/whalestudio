import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private lemma mem_fixL_iff (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w))
    (v : LL μ) : v ∈ fixL μ w J ↔ ∀ g ∈ J, rhoL μ w g v = v := by
  simp [fixL, fixF, rhoL, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]

private lemma co_integral (w : Pl K) : CO (GLnLocal.integralGL (w.adicCompletion K) n) :=
  ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩

private lemma isChr_one {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) : IsChr J (1 : G → ℂ) :=
  ⟨IsLocallyConstant.const (1 : ℂ), fun _ _ => by simp, fun _ _ _ _ => by simp⟩

private lemma exists_local_level (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (w : Pl K) :
    ∃ U : Subgroup (Gw n w), CO U ∧ U ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ V ⊓ fixL μ w U ≠ ⊥ := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  let P : TopologicalSpace.PositiveCompacts (Gw n w) :=
    { carrier := GLnLocal.integralGL (w.adicCompletion K) n
      isCompact' := GLnLocal.isCompact_integralGL _ n
      interior_nonempty' := by
        rw [(GLnLocal.isOpen_integralGL _ n).interior_eq]
        exact ⟨1, Subgroup.one_mem _⟩ }
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := occursBasics K n μ V w (Measure.haarMeasure P) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)
  let U : Subgroup (Gw n w) := stabilizerOf σ.ρ x ⊓ GLnLocal.integralGL (w.adicCompletion K) n
  have hUo : IsOpen (U : Set (Gw n w)) := by
    rw [Subgroup.coe_inf]
    exact (σ.smooth x).inter (GLnLocal.isOpen_integralGL _ n)
  have hUc : IsCompact (U : Set (Gw n w)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo)
      (by rw [Subgroup.coe_inf]; exact Set.inter_subset_right)
  refine ⟨U, ⟨hUc, hUo⟩, inf_le_right, fun hb => hx ?_⟩
  have hm : f x ∈ V ⊓ fixL μ w U := by
    refine Submodule.mem_inf.2 ⟨hfV x, (mem_fixL_iff μ w U _).2 fun g hg => ?_⟩
    rw [← hfe g x]
    exact congrArg f hg.1
  rw [hb] at hm
  exact (Submodule.mem_bot ℂ).1 hm

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.levelEx :
    UpperTheory.ConvolutionTheory.T.LevelEx := by
  intro K _ _ n μ _ V hV S hS
  choose U₀ hU₀ hU₀le hU₀ne using fun w : Pl K => exists_local_level μ V hV w
  let J : ∀ w : Pl K, Subgroup (Gw n w) := fun w =>
    if w ∈ S then U₀ w else GLnLocal.integralGL (w.adicCompletion K) n
  have hJin : ∀ w ∈ S, J w = U₀ w := fun w hw => if_pos hw
  have hJout : ∀ w, w ∉ S → J w = GLnLocal.integralGL (w.adicCompletion K) n := fun w hw => if_neg hw
  have hco : ∀ w, CO (J w) := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ w
    · rw [hJout w hw]; exact co_integral w
  have hle : ∀ w, J w ≤ GLnLocal.integralGL (w.adicCompletion K) n := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀le w
    · rw [hJout w hw]
  have heig : ∀ w, eigL μ w (J w) 1 = fixL μ w (J w) := fun w =>
    (eigBasic K n μ w (J w) 1 (hco w) (isChr_one _)).2.1
  have hloc : ∀ w, V ⊓ eigL μ w (J w) 1 ≠ ⊥ := fun w => by
    rw [heig w]
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ne w
    · rw [hJout w hw]; exact hS w hw
  have hall := typedEx K n μ V hV J (fun _ => 1) (fun w => ⟨hco w, isChr_one _⟩)
    ((S.finite_toSet.eventually_cofinite_notMem).mono fun w hw => ⟨hJout w hw, rfl⟩) hloc
  refine ⟨J, fun w => ⟨hco w, hle w⟩, fun hb => hall (eq_bot_iff.2 ?_)⟩
  rw [← hb]
  refine le_inf (le_inf inf_le_left ?_) ?_
  · refine inf_le_right.trans (le_iInf₂ fun w hw => (iInf_le _ w).trans ?_)
    rw [heig w, hJout w hw]
  · refine inf_le_right.trans (le_iInf₂ fun w _ => (iInf_le _ w).trans ?_)
    rw [heig w]
