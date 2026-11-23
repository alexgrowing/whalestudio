import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKAnisoAdd

theorem polData_le_schA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem I'_add : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 →
    ∀ Φ₁ ∈ PolData B G.M', ∀ Φ₂ ∈ PolData B G.M', G.M'.I om' (Φ₁ + Φ₂) = G.M'.I om' Φ₁ + G.M'.I om' Φ₂ := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT hq Φ₁ h₁ Φ₂ h₂
  have hV' := GlobalTheory.ThK.Inhab.pairV' hT
  have conv : ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), G.M'.Conv om' Φ := fun Φ hΦ =>
    ((GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hV' (Or.inr (by simp [hq]))).1 Φ hΦ).1
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a')) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  have s₁ := polData_le_schA G.M' hT.geo.hM' h₁
  have s₂ := polData_le_schA G.M' hT.geo.hM' h₂
  funext h
  have e : ∀ g, theta om' (Φ₁ + Φ₂) g h = theta om' Φ₁ g h + theta om' Φ₂ g h := fun g => by
    simp only [theta, map_add]
    exact thetaSum_add F (pres _ _ s₁) (pres _ _ s₂)
  simp only [Model.I, Pi.add_apply, e]
  exact integral_add (conv Φ₁ s₁ h) (conv Φ₂ s₂ h)

end GlobalTheory.ThKAnisoAdd

end
