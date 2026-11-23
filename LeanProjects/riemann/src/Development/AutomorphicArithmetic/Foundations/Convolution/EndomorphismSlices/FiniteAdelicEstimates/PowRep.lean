import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt

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

theorem powRep : PowRep := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hφ hR hU
  obtain ⟨-, -, hpt, hval, -⟩ := ptOk E a b l₁ l₂ D A
  obtain ⟨-, -, -, -, -, hfx, -, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨hidm, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨-, hrep, hmono, hmul⟩ := repAlg E A.blk (chi l₁) (chi l₂)
  obtain ⟨hrt₁, hrt₂, -⟩ := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.rtAlg' E A.blk u₁ u₂
  have hc : 0 ≤ A.blk.c := A.c_nonneg
  have ok₁ : (A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one)).Ok :=
    hpt _ _ _ (hfx T φ _ _ hφ).1
  have ok₂ : (A.ptB (rt u₁ u₂ (A.idm S L))).Ok := by
    obtain ⟨r, hr⟩ := hrt₂ (A.ptB (A.idm S L)) (hpt _ _ _ hidm)
    exact hpt _ _ _ hr.ψ
  refine ⟨ok₁, ok₂, ?_⟩
  set t₁ := A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one) with ht₁
  set t₂ := A.ptB (rt u₁ u₂ (A.idm S L)) with ht₂
  have r₁0 : 0 ≤ max t₁.T t₁.r := le_max_of_le_left ok₁.T
  have r₂0 : 0 ≤ max t₂.T t₂.r := le_max_of_le_left ok₂.T
  have base₁ : Rep A.blk (chi l₁) (chi l₂) t₁.ψ 1 (max t₁.T t₁.r) t₁.op := by
    have := hrep t₁ ok₁
    rwa [hval] at this
  have base₂ : Rep A.blk (chi l₁) (chi l₂) t₂.ψ 1 (max t₂.T t₂.r) t₂.op := by
    have := hrep t₂ ok₂
    rwa [hval] at this
  have step : ∀ k : ℕ, Rep A.blk (chi l₁) (chi l₂)
      (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) 1
      (max t₁.T t₁.r + k * (R + A.blk.c)) (t₁.op * U ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
      exact base₁
    | succ k ih =>
      have h := hmul _ _ _ _ _ _ _ _ ih hU
      rw [(hfx T φ _ _ hφ).2.2 e₁ e₂, one_mul] at h
      have e : max t₁.T t₁.r + (k : ℝ) * (R + A.blk.c) + R + A.blk.c =
          max t₁.T t₁.r + ((k + 1 : ℕ) : ℝ) * (R + A.blk.c) := by
        push_cast; ring
      rw [e, mul_assoc, ← pow_succ] at h
      exact h
  refine ⟨max t₁.T t₁.r + max t₂.T t₂.r + A.blk.c, R + A.blk.c, by positivity, by positivity, fun k => ?_⟩
  have h := hmul _ _ _ _ _ _ _ _ (step k) base₂
  rw [one_mul] at h
  have hψ : mulF A.blk.ν (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) t₂.ψ =
      rt u₁ u₂ (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) := by
    show mulF A.blk.ν _ (rt u₁ u₂ (A.idm S L)) = _
    rw [hrt₁, (hfx T φ _ _ hφ).2.1]
  rw [hψ] at h
  refine hmono _ _ _ _ _ (le_of_eq ?_) h
  ring

end UpperTheory.Zero.ConvolutionTheory.EB
