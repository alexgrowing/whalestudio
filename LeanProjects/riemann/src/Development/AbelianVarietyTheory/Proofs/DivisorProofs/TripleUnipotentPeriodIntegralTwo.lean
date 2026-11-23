import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CtMulLeftUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_unipotent_period_integral_two : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ n ∈ unip σ G.W H', ∀ h : UA σ G.W.J, GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ) (n * h) = GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ) h := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA Φ hΦ μ 𝓕 hμ h𝓕 h1 n hn h
  have hp := GlobalTheory.ThK.Inhab.pairV' hT
  have hS : Φ ∈ schA F (Fin a' × Fin (a + a')) := by
    have hle : G.M'.So B.ψ B.τ₁ ≤ schA F (Fin a' × Fin (a + a')) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, φ, h1, h2, -, rfl⟩
      exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hp.good.std).mono fun w hw => hw.1.trans hw.2)
    exact hle hΦ
  have hf : ∀ γ ∈ ratU σ G.W.J, ∀ y, G.M'.I om' Φ (γ * y) = G.M'.I om' Φ y := by
    intro γ hγ y
    unfold Model.I
    congr 1
    funext x
    simp only [theta]
    have e : om' (x, γ * y) Φ = om' (1, γ) (om' (x, y) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact GlobalTheory.T.thetaSum_invariant_rational_unitary hK.base F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ hp 1 (one_mem _) γ hγ _
      (hp.weil.isUSplitting.pres _ _ hS)
  have hc := GlobalTheory.T.constant_term_unipotent_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA (G.M'.I om' Φ) hf μ 𝓕 hμ h𝓕 h1
  exact GlobalTheory.CTInv.ct_mul_left_unip F E σ (a + a') d₁ G.W H' (G.M'.I om' Φ) (GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ)) hc
    ⟨μ, 𝓕, hμ, h𝓕, h1⟩ n hn h
