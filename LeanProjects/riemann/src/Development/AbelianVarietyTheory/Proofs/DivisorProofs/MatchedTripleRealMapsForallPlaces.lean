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

namespace GlobalTheory.ThKKer

theorem kerZero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Ψ ∈ (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}), G.M'.I om' Ψ = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Ψ hΨ
  have hT := hM.triple
  have hdec := (GlobalTheory.T.theta_kernel_decay hKP F E σ B a a' G X om om' hT).2
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres x Φ hΦ
  have hPol : PolData B G.M' ≤ schA F (Fin a' × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)
  have key : ∀ Ψ ∈ (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}),
      Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0 := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨Submodule.zero_mem _, ?_⟩
      funext h
      simp [Model.I, theta, thetaSum]
    | add x y _ _ ihx ihy =>
      obtain ⟨hxD, hx0⟩ := ihx
      obtain ⟨hyD, hy0⟩ := ihy
      refine ⟨Submodule.add_mem _ hxD hyD, ?_⟩
      have hxS := hPol hxD.1
      have hyS := hPol hyD.1
      funext h
      have e : ∀ g, theta om' (x + y) g h = theta om' x g h + theta om' y g h := fun g => by
        simp only [theta, map_add]
        exact thetaSum_add F (pres _ x hxS) (pres _ y hyS)
      have ix := (hdec x hxD.2).2.1 h
      have iy := (hdec y hyD.2).2.1 h
      have hx1 := congrFun hx0 h
      have hy1 := congrFun hy0 h
      simp only [Model.I, Pi.zero_apply] at hx1 hy1 ⊢
      rw [show (fun g => theta om' (x + y) g h) = fun g => theta om' x g h + theta om' y g h from funext e,
        integral_add ix iy, hx1, hy1, add_zero]
    | smul c x _ ih =>
      obtain ⟨hxD, hx0⟩ := ih
      refine ⟨Submodule.smul_mem _ c hxD, ?_⟩
      funext h
      have hx1 := congrFun hx0 h
      simp only [Model.I, Pi.zero_apply] at hx1 ⊢
      have e : ∀ g, theta om' (c • x) g h = c * theta om' x g h := fun g => by
        simp only [theta, map_smul]
        exact thetaSum_smul F c _
      simp only [e, integral_const_mul, hx1, mul_zero]
  exact (key Ψ hΨ).2

end GlobalTheory.ThKKer
