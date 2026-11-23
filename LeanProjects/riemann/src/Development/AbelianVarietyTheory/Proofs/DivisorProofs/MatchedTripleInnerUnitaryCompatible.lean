import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open MeasureTheory

noncomputable section

namespace GlobalTheory.ThKLinV

theorem thetaIntegral_linear : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ₂ ∈ GlobalTheory.ThK.PolData B G.M, ∀ c : ℂ, G.M.I om (Ψ₁ + Ψ₂) = G.M.I om Ψ₁ + G.M.I om Ψ₂ ∧ G.M.I om (c • Ψ₁) = c • G.M.I om Ψ₁ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ Ψ hΨ c
  have hT := hM.triple
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    left
    omega
  have hconv := (GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond).1
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om x Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil).pres x Φ hΦ
  have hPol : PolData B G.M ≤ schA F (Fin a × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2)
  have hΦS := hPol hΦ
  have hΨS := hPol hΨ
  refine ⟨?_, ?_⟩
  · funext h
    have e : ∀ g, theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun g => by
      simp only [theta, map_add]
      exact thetaSum_add F (pres _ Φ hΦS) (pres _ Ψ hΨS)
    have iΦ := (hconv Φ hΦS).1 h
    have iΨ := (hconv Ψ hΨS).1 h
    simp only [Model.I, Pi.add_apply]
    rw [show (fun g => theta om (Φ + Ψ) g h) = fun g => theta om Φ g h + theta om Ψ g h from funext e,
      integral_add iΦ iΨ]
  · funext h
    have e : ∀ g, theta om (c • Φ) g h = c * theta om Φ g h := fun g => by
      simp only [theta, map_smul]
      exact thetaSum_smul F c _
    simp only [Model.I, Pi.smul_apply, smul_eq_mul]
    rw [show (fun g => theta om (c • Φ) g h) = fun g => c * theta om Φ g h from funext e, integral_const_mul]

end GlobalTheory.ThKLinV

end
