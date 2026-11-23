import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormFullRootFactor
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormWindow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticRootBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormFullBranchConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialRootPredicateFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormFullRootFactor.proof (hWin : PrimitiveFormWindow.Statement)
    (hBr : AnalyticRootBranch.Statement) (hConst : PrimitiveFormFullBranchConstant.Statement)
    (hFac : PolynomialRootPredicateFactor.Statement) : PrimitiveFormFullRootFactor.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδne hP hsep hQ
  obtain ⟨W, B, N', k, f, hWo, hwW, hBo, hBc, hAwB, hN'o, hcl, hf, hXN, hsph, hPW, -, haB, hδB, hqB,
    hsepB⟩ := hWin σ X w d A hX hiso ℓ N a δ q ha hδ hq hP hsep hQ
  have hex : ∃ t ∈ B, δ t ≠ 0 := by
    by_contra h
    push Not at h
    exact hδne (Filter.mem_of_superset (hBo.mem_nhds hAwB) h)
  have hloc : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧
          (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ PrimitiveFormRootFull X W A ℓ δ q t₀ τ₀) := by
    intro t₀ ht₀ hδt₀ τ₀ hτ₀
    obtain ⟨O, r, hOo, ht₀O, hr, hrt₀, hroot⟩ :=
      hBr d N a t₀ τ₀ (fun j => haB j t₀ ht₀) (hsepB t₀ ht₀ hδt₀) hτ₀
    have hU : IsOpen (O ∩ (B ∩ δ ⁻¹' {0}ᶜ)) :=
      hOo.inter (hδB.continuousOn.isOpen_inter_preimage hBo isOpen_compl_singleton)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t₀ ⟨ht₀O, ht₀, hδt₀⟩
    have hsub : ∀ s ∈ Metric.ball t₀ ε, s ∈ O ∧ s ∈ B ∧ δ s ≠ 0 := fun s hs =>
      ⟨(hball hs).1, (hball hs).2.1, (hball hs).2.2⟩
    have hc := hConst σ X W N' k f d A ℓ N a δ q B (Metric.ball t₀ ε) r hWo hN'o hcl hf hXN hsph hPW hBo
      haB hδB hqB Metric.isOpen_ball (convex_ball t₀ ε).isPreconnected (fun s hs => (hsub s hs).2.1)
      (fun s hs => (hsub s hs).2.2) (fun s hs => hsepB s (hsub s hs).2.1 (hsub s hs).2.2)
      (hr.mono fun s hs => (hsub s hs).1) (fun s hs => hroot s (hsub s hs).1)
    refine ⟨Metric.ball t₀ ε, r, Metric.isOpen_ball, Metric.mem_ball_self hε,
      hr.continuousOn.mono fun s hs => (hsub s hs).1, hrt₀, fun s hs => ⟨hroot s (hsub s hs).1, ?_⟩⟩
    rw [← hrt₀]
    exact hc s hs t₀ (Metric.mem_ball_self hε)
  obtain ⟨C, E, hCE, hprod, hzero⟩ :=
    hFac d N B a δ (PrimitiveFormRootFull X W A ℓ δ q) hBo hBc haB hδB hex hsepB hloc
  exact ⟨W, B, C, E, hWo, hwW, hBo, hAwB, hCE, hprod, hzero⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
