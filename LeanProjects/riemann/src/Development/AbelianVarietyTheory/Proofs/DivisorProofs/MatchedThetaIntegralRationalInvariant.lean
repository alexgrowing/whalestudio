import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section

namespace GlobalTheory.ThK.LiftConstLeft

theorem thLift_rat_left : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ Φ₁' ∈ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)) (f : UA σ G.W.J → ℂ),
      ∀ γ ∈ ratU σ G.V'.J, ∀ g, thLift om' Φ₁' μ 𝓕 f (γ * g) = thLift om' Φ₁' μ 𝓕 f g := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ μ 𝓕 f γ hγ g
  have hP := GlobalTheory.ThKContSmall.isPair_small hM.triple
  have hS := hP.weil.isUSplitting
  have hΦA : Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    GlobalTheory.ThKContSmall.so_le_schA hM.triple.geo.hM' B.τ₁ hΦ
  have key : ∀ h, theta om' Φ (γ * g) h = theta om' Φ g h := fun h => by
    have e : om' (γ * g, h) Φ = om' (γ, 1) (om' (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    simp only [theta]
    rw [e, GlobalTheory.T.thetaSum_invariant_rational_unitary hKP.base F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP γ hγ 1 (one_mem _) _ (hS.pres _ _ hΦA)]
  simp only [thLift_def, key]

end GlobalTheory.ThK.LiftConstLeft
