import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwiseStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchProdRule

open Filter Topology

theorem slope_prod {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ (k : ℕ) (T : Fin k → ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) (Q : Fin k → SchwartzMap V ℂ → SchwartzMap V ℂ),
    (∀ i t, Continuous (T i t)) → (∀ i f, T i 0 f = f) →
    (∀ i f, Tendsto (fun t : ℝ => t⁻¹ • (T i t f - f)) (𝓝[≠] 0) (𝓝 (Q i f))) →
    ∀ f, Tendsto (fun t : ℝ => t⁻¹ • ((List.ofFn fun i => T i t).prod f - f)) (𝓝[≠] 0) (𝓝 (∑ i, Q i f)) := by
  intro k
  induction k with
  | zero =>
    intro T Q _ _ _ f
    simpa using (tendsto_const_nhds (x := (0 : SchwartzMap V ℂ)) (f := 𝓝[≠] (0 : ℝ)))
  | succ k ih =>
    intro T Q hc h0 hQ f
    have ht := ih (fun i => T i.succ) (fun i => Q i.succ) (fun i => hc i.succ) (fun i => h0 i.succ)
      (fun i => hQ i.succ) f
    let S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ := fun t => ⟨T 0 t, hc 0 t⟩
    have hS1 : ∀ g, Tendsto (fun t => S t g) (𝓝[≠] 0) (𝓝 g) := by
      intro g
      have h2 : Tendsto (fun t : ℝ => t • (t⁻¹ • (T 0 t g - g)) + g) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • Q 0 g + g)) :=
        ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hQ 0 g)).add_const g
      rw [zero_smul, zero_add] at h2
      refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
      rfl
    have h1 := GlobalTheory.T.schwartz_tendsto_operatorCurve_of_pointwise V S hS1 _ _ ht
    have h3 := h1.add (hQ 0 f)
    rw [Fin.sum_univ_succ, add_comm (Q 0 f)]
    refine h3.congr fun t => ?_
    have e : (List.ofFn fun i => T i t).prod f = T 0 t ((List.ofFn fun i : Fin k => T i.succ t).prod f) := by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    rw [e]
    show T 0 t (t⁻¹ • ((List.ofFn fun i : Fin k => T i.succ t).prod f - f)) + _ = _
    rw [LinearMap.map_smul_of_tower, map_sub, ← smul_add, sub_add_sub_cancel]

open scoped Classical in

theorem hasDerivAt_prod : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW k γ hγ T hT hadd h0 f y c hc
  have hQ : ∀ i g, ∃ q, Tendsto (fun t : ℝ => t⁻¹ • (T i t g - g)) (𝓝[≠] 0) (𝓝 q) := fun i g =>
    GlobalTheory.T.weil_line_cm_model_action hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i) g
  choose Q hQ using hQ
  have hcont : ∀ i t, Continuous (T i t) := fun i =>
    GlobalTheory.T.weil_line_cm_model_sum hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i)
  have hprod := slope_prod k T Q hcont h0 hQ f
  let ev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
  have hev : ∀ (s : ℝ) (g h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), ev (s • (g - h)) = s • (g y - h y) := by
    intro s g h
    rw [ContinuousLinearMap.map_smul_of_tower, map_sub]
    rfl
  have hevq : ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ev g = g y := fun g => rfl
  have hci : ∀ i, c i = Q i f y := by
    intro i
    have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hc i)
    have h2 := (ev.continuous.tendsto _).comp (hQ i f)
    rw [hevq] at h2
    simp only [zero_add, h0] at h1
    refine tendsto_nhds_unique h1 (h2.congr fun t => ?_)
    exact hev _ _ _
  have hsum : (∑ i, c i) = ev (∑ i, Q i f) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (hci i).trans (hevq _).symm
  rw [hasDerivAt_iff_tendsto_slope_zero, hsum]
  have hp0 : (List.ofFn fun i => T i 0).prod = 1 := by
    have e : (fun i => T i 0) = fun _ => (1 : Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) :=
      funext fun i => LinearMap.ext (h0 i)
    rw [e, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 := (ev.continuous.tendsto _).comp hprod
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, zero_add, hp0]
  exact hev _ _ _

end GlobalTheory.ArchProdRule
