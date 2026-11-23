import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepSourceLineEqOppositeTargetLineStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SeeLastPf

theorem ofAdj_zero (D : D7) (L S : HSp D) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S 0 = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]

theorem seeLast : ∀ D : D7, SeeLast D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hT hz'' Ξ Φ₂ hΞ hΦ₂
  have hψ : IsStdChar D ψ (-1) := h₁.std
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ V₀ A L o S
  have htgt := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ X T L'' o'' S
  have hτ' : τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; simp
  have hrk : L.rank = L''.rank := hL.trans hL''.symm
  have hline := fun u => GlobalTheory.T.weilRep_sourceLine_eq_opposite_targetLine D ψ L L'' S τ hrk hτ' χz χS χS' omz omz'' hz hz''
    (fun v => Ξ ((o.resS S).symm (u, v))) ((hsrc.slice_theta Ξ hΞ).2 u)
  refine ⟨fun u => (hline u).1, ?_⟩
  intro h₀ h h'
  have e1 : ∀ u, omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
      (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) 0 =
      omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0 := by
    intro u
    rw [htgt.om_box χS' χT χz⁻¹ omX omT omz'' hX hT hz'' h h' 1 Φ₂ _ hΦ₂ (hline u).1, htgt.box_zero,
      (hline u).2 h]
    beta_reduce
    congr 1
    exact congrArg (omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))))
      ((congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S) (Matrix.mul_zero _)).trans (ofAdj_zero D L S))
  have e2 := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz h₀ 1 h Ξ hΞ 0).2 0
  have e0 : (o.resS S).symm (0, 0) = 0 := by
    rw [← Prod.zero_eq_mk, map_zero]
  rw [e0] at e2
  simp only [e1]
  rw [e2]
  have : (fun u => omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0) =
      omT (h, h') Φ₂ 0 • (fun u' => omz (1, h) (fun v' => Ξ ((o.resS S).symm (u', v'))) 0) := by
    funext u; simp
  rw [this, map_smul]
  simp

end GlobalTheory.SeeLastPf

end
