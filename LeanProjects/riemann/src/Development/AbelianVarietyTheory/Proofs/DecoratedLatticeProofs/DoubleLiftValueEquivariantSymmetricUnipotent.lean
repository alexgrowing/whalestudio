import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralMulRightN
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep

open GlobalTheory.NormalFramePeriod in

theorem valK_nEquiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ Ξ, ∀ g ∈ N Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ (rTrans (Q.gl₂ g) f) = (Q.ψk (simpleSum g) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f := by
  intro D ψ hψ σ S Q c₁ c₂ _ _ φ _ Λ _ Ξ g hg f hf
  have hc : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, rTrans_one] at this
  unfold valK
  rw [per_flagN S.B' ψ hψ _ f hc.1 (GlobalTheory.LocGrp.mem_flagN_of_mem_N (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)),
    GlobalTheory.LocBesChar.psiBes_isLoc D Q.k (ofSplit Q.q) ψ Q.ψk Q.char σ S.B' _ Q.n₂ (Q.c + 1) Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)]

end GlobalTheory.TriStep
end
