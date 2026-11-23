import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalStabiliserScalesRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalLeviScalingIsotropicFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScalingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLeviMatrixActionIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRes

theorem res_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (n : NI V C) (f : WO V W → ℂ), IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω ((n : GA D V), 1) f) = res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ n f hf
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hs
  obtain ⟨a, haQ, haC, haB, haC'⟩ := GlobalTheory.T.exists_rationalLevi_scaling_isotropicFrame D V V' r C C' B hs h1 h2 h3
  obtain ⟨l, hl⟩ := GlobalTheory.T.thetaRestriction_invariant_rationalLeviScaling D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hμ
  have hp : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (ω p f) := hω.om_pres
  have hm : ∀ x y : GA D V, ∀ f, ω (x * y, 1) f = ω (x, 1) (ω (y, 1) f) := by
    intro x y f
    rw [show ((x * y, 1) : GA D V × GA D W) = (x, 1) * (y, 1) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ g ∈ NI V C, ∀ f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (g, 1) f) = res V V' W C B μ 𝓨 f := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨m, hmN, rfl⟩ := GlobalTheory.T.unipotent_levi_matrix_action_identity D V V' r C C' B hs h1 h2 h3 a haC haB haC' x hx1 hx2 hx3
      obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentRadical_stabiliser_scales_restriction D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ m hmN
      intro f hf
      have e1 : res V V' W C B μ 𝓨 (ω (a, 1) (ω (a⁻¹, 1) (ω (m⁻¹, 1) f))) = res V V' W C B μ 𝓨 (ω (m⁻¹, 1) f) := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      have e2 : res V V' W C B μ 𝓨 (ω (m, 1) (ω (m⁻¹, 1) f)) = res V V' W C B μ 𝓨 f := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      rw [hm, hm, hm, hl _ (hp _ _ (hp _ _ (hp _ _ hf))), hc _ (hp _ _ (hp _ _ hf)), smul_smul, mul_comm,
        ← smul_smul, ← hl _ (hp _ _ (hp _ _ hf)), e1, ← hc _ (hp _ _ hf), e2]
    | one => intro f hf; rw [show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
    | mul x y _ _ hx hy => intro f hf; rw [hm, hx _ (hp _ _ hf), hy _ hf]
    | inv x _ hx =>
      intro f hf
      have := hx (ω (x⁻¹, 1) f) (hp _ _ hf)
      rw [← this, ← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
  exact key n n.2 f hf
end GlobalTheory.UnipRes
