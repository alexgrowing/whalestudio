import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.DblBoxTheta

open GlobalTheory.DblBox

theorem isThetaFunO_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
    Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      Formalism.IndefR.Datum.IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (GlobalTheory.DblBox.box f₁ f₂) := by
  intro D ψ hψ S T f₁ f₂ h₁ h₂
  have ctop : Continuous (top : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  have cbot : Continuous (bot : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  let topH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' top top_add
  let botH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' bot bot_add
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    have e₁ : top (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
    have e₂ : bot (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
    simp only [box, top_add, bot_add, symplOH_dbl]
    rw [e₁, e₂, h₁.quasi, h₂.quasi]
    rw [sub_eq_add_neg, neg_add, AddChar.map_add_eq_mul, neg_neg]
    simp only [psi_neg hψ, star_mul', star_star]
    ring
  · obtain ⟨U₁, hU₁o, hU₁⟩ := h₁.level
    obtain ⟨U₂, hU₂o, hU₂⟩ := h₂.level
    refine ⟨U₁.comap topH ⊓ U₂.comap botH, ?_, ?_⟩
    · exact (hU₁o.preimage ctop).inter (hU₂o.preimage cbot)
    · intro u hu hinf
      have hu₁ : top u ∈ U₁ := hu.1
      have hu₂ : bot u ∈ U₂ := hu.2
      have ht : (top u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inl i))) j
      have hb : (bot u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inr i))) j
      rw [heisO_box hψ, hU₁ _ hu₁ ht, hU₂ _ hu₂ hb]
  · exact (h₁.cont.comp ctop).mul ((h₂.cont.comp cbot).star)
  · intro k L hL hfin w
    have hf₁ :=
      h₁.smooth k (topH.comp L) (ctop.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inl i))) j) (top w)
    have hf₂ :=
      h₂.smooth k (botH.comp L) (cbot.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inr i))) j) (bot w)
    exact ContDiff.mul hf₁ (Complex.conjCLE.contDiff.comp hf₂)

end GlobalTheory.DblBoxTheta
