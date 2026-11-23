import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

variable {F : Type} [Field F] [NumberField F]

private theorem slice_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) :
    (fun s => g (Function.update v 1 s)) ∈ finiteSchwartzBruhat F := by
  obtain ⟨hl, hc⟩ := hg
  have hcont : Continuous fun s : FiniteAdeleRing (𝓞 F) F => Function.update v 1 s :=
    continuous_const.update 1 continuous_id
  refine ⟨hl.comp_continuous hcont, ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image (continuous_apply 1)) fun s hs => ?_
  by_contra h
  exact hs ⟨Function.update v 1 s, subset_tsupport _ h, by simp⟩

private noncomputable def T (g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : Fin 4 → FiniteAdeleRing (𝓞 F) F) : ℂ :=
  finiteFourier F (fun s => g (Function.update v 1 s)) (-(v 1))

private theorem T_tensor (h : Fin 4 → FiniteAdeleRing (𝓞 F) F → ℂ) :
    T (finiteTensor h) =
      finiteTensor ![h 0, fun x => finiteFourier F (h 1) (-x), h 2, h 3] := by
  funext v
  have hs : ∀ s, finiteTensor h (Function.update v 1 s) * (finiteAdelicChar F (s * -(v 1)) : ℂ) =
      (h 0 (v 0) * h 2 (v 2) * h 3 (v 3)) * (h 1 s * (finiteAdelicChar F (s * -(v 1)) : ℂ)) := by
    intro s
    simp [finiteTensor, Fin.prod_univ_four, Function.update_apply]
    ring
  simp only [T, finiteFourier]
  simp_rw [hs]
  rw [integral_const_mul]
  simp [finiteTensor, Fin.prod_univ_four, finiteFourier]
  ring

private theorem neg_mem {f : FiniteAdeleRing (𝓞 F) F → ℂ} (hf : f ∈ finiteSchwartzBruhat F) :
    (fun x => f (-x)) ∈ finiteSchwartzBruhat F :=
  ⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg _)⟩

private theorem T_mem {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    T g ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  have hsub := (finiteSchwartzBruhatPi_eq_span (K := F) (ι := Fin 4)).ge
  rw [finiteSchwartzBruhatPi_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨J, a⟩, rfl⟩ := hf
    rw [T_tensor]
    refine finiteTensor_mem fun i => ?_
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact neg_mem (finiteFourier_mem_finiteSchwartzBruhat
        (cosetIndicator_mem_finiteSchwartzBruhat J _))
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
    · exact cosetIndicator_mem_finiteSchwartzBruhat J _
  | zero =>
    have : T (0 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
      funext v
      simp [T, finiteFourier]
    rw [this]
    exact zero_mem _
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    have : T (f₁ + f₂) = T f₁ + T f₂ := by
      funext v
      exact congrFun (finiteFourier_add
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₁) v))
        (integrable_of_mem_finiteSchwartzBruhat (slice_mem (hsub h₂) v))) _
    rw [this]
    exact add_mem ih₁ ih₂
  | smul c f _ ih =>
    have : T (c • f) = c • T f := by
      funext v
      simp only [T, finiteFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    rw [this]
    exact Submodule.smul_mem _ c ih

end UpperTheory.ConvolutionTheory.R2.G.FiniteFourierHat

theorem UpperTheory.ConvolutionTheory.R2.G.finHat :
    ∀ (F : Type) [Field F] [NumberField F], ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), (∀ v, Integrable (fun s => g (Function.update v 1 s)) (finiteAdeleMeasure F)) ∧
    (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) ∈ finiteSchwartzBruhatPi F (ι := Fin 4) := by
  intro F _ _ g hg
  refine ⟨fun v => integrable_of_mem_finiteSchwartzBruhat (FiniteFourierHat.slice_mem hg v), ?_⟩
  have he : (fun v => ∫ s, g (Function.update v 1 s) * ((finiteAdelicChar F (-(s * v 1)) : Circle) : ℂ) ∂(finiteAdeleMeasure F)) = FiniteFourierHat.T g := by
    funext v
    simp only [FiniteFourierHat.T, finiteFourier, mul_neg]
  rw [he]
  exact FiniteFourierHat.T_mem hg
