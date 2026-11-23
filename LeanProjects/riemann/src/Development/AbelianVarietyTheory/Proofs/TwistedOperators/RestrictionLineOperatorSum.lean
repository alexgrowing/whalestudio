import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsExtra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    {m : ℕ} (φ : Fin m → (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ u (∑ i, φ i) = ∑ i, M.co.rho ψ u (φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem rho_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    M.co.rho ψ u 0 = 0 := by
  funext x
  simp only [Darboux.rho, schr, Pi.zero_apply, mul_zero]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ)
    (f c' : SInf F κ) (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c'))
    (T : SInf F κ →L[ℂ] ℂ) : HasDerivAt (fun t => T (c t)) (T c') 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hT := ((T.restrictScalars ℝ).continuous.tendsto c').comp hl
  refine hT.congr fun t => ?_
  simp only [Function.comp_apply, slope_def_module, sub_zero, hc0]
  rw [← map_sub]
  exact (T.restrictScalars ℝ).map_smul t⁻¹ (c t - f)

theorem hasDerivAt_eval {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (y : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t => c t y) (c' y) 0 := by
  have h := hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl
    ((BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))
  simpa using h

theorem hasDerivAt_clm {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (T : SInf F κ →L[ℂ] ℂ) :
    HasDerivAt (fun t => T (c t)) (T c') 0 :=
  hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl T

private theorem exists_ne_zero_smul_mem_of_mem_span' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (om : Rep σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f f₁ : SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ) (hR : Rest (evI F) (⇑f) r)
    (hD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑f) (⇑f₁))
    (horb : ∃ (c : ℝ → SInf F (Fin n × Fin d)) (c' : SInf F (Fin n × Fin d)), c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c') ∧
      ∀ t : ℝ, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) (⇑f) (⇑(c t)))
    (hclm : f ≠ 0 → ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ g : SInf F (Fin n × Fin d),
      HasSum (fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑g) r) (fun i => algebraMap F (AF F) (ξ i))) (T g)) :
    (∀ t : ℝ, Summable fun ξ : Fin n × Fin d → F =>
      M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r)) (fun i => algebraMap F (AF F) (ξ i))) ∧
    (Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u (tens (evI F) (⇑f₁) r) (fun i => algebraMap F (AF F) (ξ i))) ∧
    HasDerivAt (fun t : ℝ => thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r))))
      (thetaSum F (M.co.rho ψ u (tens (evI F) (⇑f₁) r))) 0 := by
  obtain ⟨c, c', hc0, hl, hc⟩ := horb
  have hcr : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r) = tens (evI F) (⇑(c t)) r :=
    fun t => hc t r hR
  have hder : ∀ x, HasDerivAt (fun t : ℝ => tens (evI F) (⇑(c t)) r x) (tens (evI F) (⇑c') r x) 0 := fun x =>
    (hasDerivAt_eval c f c' hc0 hl (fun j => evI F (x j))).mul_const (r x)
  have hf₁ : tens (evI F) (⇑f₁) r = tens (evI F) (⇑c') r := by
    funext x
    have h1 := hD r hR x
    simp only [hcr] at h1
    exact h1.unique (hder x)
  by_cases hf : f = 0
  · have hz : tens (evI F) (⇑f) r = 0 := by
      funext x
      simp [tens, hf]
    have h0 : ∀ t : ℝ, tens (evI F) (⇑(c t)) r = 0 := by
      intro t
      rw [← hcr t, hz, map_zero]
    have hc'0 : tens (evI F) (⇑c') r = 0 := by
      funext x
      have h3 : HasDerivAt (fun t : ℝ => tens (evI F) (⇑(c t)) r x) 0 0 := by
        simp only [h0, Pi.zero_apply]
        exact hasDerivAt_const _ _
      exact (hder x).unique h3
    refine ⟨fun t => ?_, ?_, ?_⟩
    · simp only [hcr, h0, rho_zero, Pi.zero_apply]
      exact summable_zero
    · simp only [hf₁, hc'0, rho_zero, Pi.zero_apply]
      exact summable_zero
    · simp only [hcr, h0, hf₁, hc'0, rho_zero, thetaSum, Pi.zero_apply, tsum_zero]
      exact hasDerivAt_const _ _
  · obtain ⟨T, hT⟩ := hclm hf
    refine ⟨fun t => ?_, ?_, ?_⟩
    · rw [hcr t]
      exact (hT (c t)).summable
    · rw [hf₁]
      exact (hT c').summable
    · have e1 : (fun t : ℝ => thetaSum F (M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r))))
          = fun t => T (c t) := by
        funext t
        rw [hcr t]
        exact (hT (c t)).tsum_eq
      have e2 : thetaSum F (M.co.rho ψ u (tens (evI F) (⇑c') r)) = T c' := (hT c').tsum_eq
      rw [e1, hf₁, e2]
      exact hasDerivAt_clm c f c' hc0 hl T

end GlobalTheory.ThetaLineDeriv

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ m f f₁ r hR hD u
  have hone := fun i => exists_ne_zero_smul_mem_of_mem_span' G.M B.ψ om γ u (f i) (f₁ i) (r i) (hR i) (hD i)
    (GlobalTheory.WeilArchSmooth.exists_orbit hP G.M B.ψ X.β (X.β / X.α) om hT.base.cm hT.base.std hT.weil γ hγ (f i))
    (fun hf => GlobalTheory.ThetaSchrCont.exists_clm_hasSum G.M B.ψ hT.base.std u (f i) (r i) (hR i) hf)
  have e1 : ∀ t : ℝ, thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i))))
      = ∑ i, thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)))) := by
    intro t
    rw [map_sum, rho_sum]
    unfold thetaSum
    simp only [Finset.sum_apply]
    exact (hasSum_sum fun i _ => ((hone i).1 t).hasSum).tsum_eq
  have e2 : thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))
      = ∑ i, thetaSum F (G.M.co.rho B.ψ u (tens (evI F) (⇑(f₁ i)) (r i))) := by
    rw [rho_sum]
    unfold thetaSum
    simp only [Finset.sum_apply]
    exact (hasSum_sum fun i _ => (hone i).2.1.hasSum).tsum_eq
  simp only [e1, e2]
  exact HasDerivAt.fun_sum fun i _ => (hone i).2.2

end GlobalTheory.ThetaLineDeriv
