import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.LinMapV

theorem exists_linearMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' →
      ∃ L : GlobalTheory.ThK.PolData B G.M →ₗ[ℂ] (UA σ G.W.J → ℂ), ∀ Φ : GlobalTheory.ThK.PolData B G.M, L Φ = G.M.I om Φ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    have h3 : min (a - G.p) G.p ≤ G.p := min_le_right _ _
    left
    omega
  have hconv := (GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond).1
  have pres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om x Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) :=
    fun x Φ hΦ => (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres x Φ hΦ
  have hPol : GlobalTheory.ThK.PolData B G.M ≤ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2)
  refine ⟨{ toFun := fun Φ => G.M.I om Φ, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · rintro ⟨Φ, hΦ⟩ ⟨Ψ, hΨ⟩
    have hΦS := hPol hΦ
    have hΨS := hPol hΨ
    funext h
    have e : ∀ g, theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun g => by
      simp only [theta, map_add]
      exact GlobalTheory.WeilM.thetaSum_add F (pres _ Φ hΦS) (pres _ Ψ hΨS)
    show G.M.I om (Φ + Ψ) h = G.M.I om Φ h + G.M.I om Ψ h
    simp only [Model.I, e]
    exact integral_add ((hconv Φ hΦS).1 h) ((hconv Ψ hΨS).1 h)
  · rintro c ⟨Φ, hΦ⟩
    funext h
    show G.M.I om (c • Φ) h = c * G.M.I om Φ h
    simp only [Model.I, theta, map_smul, GlobalTheory.WeilM.thetaSum_smul]
    exact integral_const_mul _ _

end GlobalTheory.ThK.LinMapV

end
