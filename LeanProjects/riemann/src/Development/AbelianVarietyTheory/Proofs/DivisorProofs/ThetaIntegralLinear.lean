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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKLinSo

theorem thetaIntegral_linear_So : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ Φ₁ ∈ G.M'.So B.ψ B.τ₁, ∀ Φ₂ ∈ G.M'.So B.ψ B.τ₁, ∀ c : ℂ, G.M'.I om' (c • Φ₁ + Φ₂) = c • G.M'.I om' Φ₁ + G.M'.I om' Φ₂ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT Φ hΦ Ψ hΨ c
  have hdec := (GlobalTheory.T.theta_kernel_decay hKP F E σ B a a' G X om om' hT).2
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  have hSo : G.M'.So B.ψ B.τ₁ ≤ schA F (Fin a' × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, φ, hSB, hev, -, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)
  have hΦS := hSo hΦ
  have hΨS := hSo hΨ
  have hcΦS : c • Φ ∈ schA F (Fin a' × Fin (a + a')) := Submodule.smul_mem _ c hΦS
  funext h
  have e : ∀ g, theta om' (c • Φ + Ψ) g h = c * theta om' Φ g h + theta om' Ψ g h := fun g => by
    have e1 : theta om' (c • Φ + Ψ) g h = theta om' (c • Φ) g h + theta om' Ψ g h := by
      simp only [theta, map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (pres _ (c • Φ) hcΦS) (pres _ Ψ hΨS)
    have e2 : theta om' (c • Φ) g h = c * theta om' Φ g h := by
      simp only [theta, map_smul]
      exact GlobalTheory.WeilM.thetaSum_smul F c _
    rw [e1, e2]
  have iΦ := (hdec Φ hΦ).2.1 h
  have iΨ := (hdec Ψ hΨ).2.1 h
  simp only [Model.I, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (fun g => theta om' (c • Φ + Ψ) g h) = fun g => c * theta om' Φ g h + theta om' Ψ g h from funext e,
    integral_add (iΦ.const_mul c) iΨ, integral_const_mul]

end GlobalTheory.ThKLinSo
