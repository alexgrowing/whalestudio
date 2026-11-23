import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspGrowSpace

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ ψ : GA D V → ℂ}

theorem isCuspGrow_add (h : IsCuspGrow θ V φ) (h' : IsCuspGrow θ V ψ) : IsCuspGrow θ V (φ + ψ) := by
  obtain ⟨a, s, c, g⟩ := h
  obtain ⟨a', s', c', g'⟩ := h'
  refine ⟨⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, a.left γ hγ, a'.left γ hγ], ?_, a.cont.add a'.cont⟩,
    add_mem s s', GlobalTheory.MultMem.isCuspFun_add a a' c c', ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    obtain ⟨U', hU', e'⟩ := a'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hf g => by
      rw [Pi.add_apply, Pi.add_apply, e k hk.1 hf, e' k hk.2 hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    obtain ⟨N', hN'⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g'
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨max N N', fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).add _ s _ s']
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
      ⟨ne_top_of_le_ne_top (hN l hl) (GlobalTheory.Size.growthSize_anti (le_max_left _ _)),
        ne_top_of_le_ne_top (hN' l hl) (GlobalTheory.Size.growthSize_anti (le_max_right _ _))⟩) GlobalTheory.Size.growthSize_add_le

theorem isCuspGrow_smul (z : ℂ) (h : IsCuspGrow θ V φ) : IsCuspGrow θ V (z • φ) := by
  obtain ⟨a, s, c, g⟩ := h
  refine ⟨⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, a.left γ hγ], ?_, a.cont.const_smul z⟩,
    Submodule.smul_mem _ z s, GlobalTheory.MultMem.isCuspFun_smul z c, ?_⟩
  · obtain ⟨U, hU, e⟩ := a.level
    exact ⟨U, hU, fun k hk hf g => by rw [Pi.smul_apply, Pi.smul_apply, e k hk hf]⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.Size.unifModGrowth_iff.1 g
    refine GlobalTheory.Size.unifModGrowth_iff.2 ⟨N, fun l hl => ?_⟩
    rw [(GlobalTheory.Size.linOnSm_rWord hl).smul, GlobalTheory.Size.growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top (hN l hl)

theorem isCuspGrow_zero : IsCuspGrow θ V 0 := by
  refine ⟨(isAutFunSm_const θ V 0).toIsAutFun, zero_mem _, fun _ _ _ _ _ _ _ _ => by simp,
    GlobalTheory.Size.unifModGrowth_iff.2 ⟨0, fun l hl => ?_⟩⟩
  have := (GlobalTheory.Size.linOnSm_rWord (θ := θ) hl).smul 0 0
  rw [zero_smul, zero_smul] at this
  rw [this]
  exact (GlobalTheory.Size.growthSize_const (0 : ℂ)).trans_ne enorm_ne_top

theorem isCuspGrow_of_mem_span : ∀ (D : D7) (θ : InfFam D) (V : HSp D),
    ∀ φ ∈ Submodule.span ℂ {φ | IsCuspGrow θ V φ}, IsCuspGrow θ V φ := by
  intro D θ V φ h
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isCuspGrow_zero
  | add x y _ _ hx hy => exact isCuspGrow_add hx hy
  | smul c x _ hx => exact isCuspGrow_smul c hx

end GlobalTheory.Chain.CuspGrowSpace

end
