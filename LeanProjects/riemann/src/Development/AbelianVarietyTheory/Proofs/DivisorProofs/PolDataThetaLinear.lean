import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThKLinT

open GlobalTheory.WeilM GlobalTheory.ThK in

theorem thetaIntegral_linear_of_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' →
      ∃ L : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ[ℂ] (UA σ G.W.J → ℂ),
        ∀ Φ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), L Φ = G.M'.I om' Φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT
  have hdec := (GlobalTheory.T.theta_kernel_decay hKP F E σ B a a' G X om om' hT).2
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  have hPol : PolData B G.M' ≤ schA F (Fin a' × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)
  have lin : ∀ Φ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Ψ ∈ (PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ c : ℂ,
      G.M'.I om' (Φ + c • Ψ) = G.M'.I om' Φ + c • G.M'.I om' Ψ := by
    intro Φ hΦ Ψ hΨ c
    have hΦS := hPol hΦ.1
    have hΨS := hPol hΨ.1
    have hcΨS : c • Ψ ∈ schA F (Fin a' × Fin (a + a')) := Submodule.smul_mem _ c hΨS
    funext h
    have e : ∀ g, theta om' (Φ + c • Ψ) g h = theta om' Φ g h + c * theta om' Ψ g h := fun g => by
      have e1 : theta om' (Φ + c • Ψ) g h = theta om' Φ g h + theta om' (c • Ψ) g h := by
        simp only [theta, map_add]
        exact thetaSum_add F (pres _ Φ hΦS) (pres _ (c • Ψ) hcΨS)
      have e2 : theta om' (c • Ψ) g h = c * theta om' Ψ g h := by
        simp only [theta, map_smul]
        exact thetaSum_smul F c _
      rw [e1, e2]
    have iΦ := (hdec Φ hΦ.2).2.1 h
    have iΨ := (hdec Ψ hΨ.2).2.1 h
    simp only [Model.I, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (fun g => theta om' (Φ + c • Ψ) g h) = fun g => theta om' Φ g h + c * theta om' Ψ g h from funext e,
      integral_add iΦ (iΨ.const_mul c), integral_const_mul]
  refine ⟨{ toFun := fun Φ => G.M'.I om' (Φ : _), map_add' := ?_, map_smul' := ?_ }, fun Φ => rfl⟩
  · intro Φ Ψ
    have := lin Φ Φ.2 Ψ Ψ.2 1
    simpa using this
  · intro c Φ
    have h0 := lin 0 (Submodule.zero_mem _) Φ Φ.2 c
    have h00 := lin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, zero_add] at h0 h00
    have hz : G.M'.I om' 0 = 0 := by
      have := congrArg (fun f => f - G.M'.I om' 0) h00
      simpa using this.symm
    simpa [hz] using h0

end GlobalTheory.ThKLinT

end
