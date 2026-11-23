import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open MeasureTheory

noncomputable section

namespace GlobalTheory.ThKLin

theorem thetaIntegral_linear : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ c : ℂ, G.M'.I om' (Φ + c • Ψ) = G.M'.I om' Φ + c • G.M'.I om' Ψ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ Ψ hΨ c
  have hT := hM.triple
  have hdec := (GlobalTheory.T.theta_kernel_decay hKP F E σ B a a' G X om om' hT).2
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  have hPol : PolData B G.M' ≤ schA F (Fin a' × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)
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

end GlobalTheory.ThKLin
