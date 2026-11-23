import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.ThetaCarry

theorem continuous_reW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b : WO (reS S b) T → WO S T) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun x : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D)))

theorem reW_ratW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reW S T b (ratW T (reS S b) γ) = ratW T S (γ * frPinv S b) := by
  unfold reW ratW
  rw [Matrix.map_mul]
  rfl

theorem reW_map_inf {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (infPart D) = 0) : (reW S T b u).map (infPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := infPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (infPart D) = 0 from hu, Matrix.zero_mul]

theorem reW_map_fin {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (finPart D) = 0) : (reW S T b u).map (finPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := finPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (finPart D) = 0 from hu, Matrix.zero_mul]

theorem isThetaFunO_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := by
  intro D ψ S T b hs f hf
  have hsH : ∀ x y : WO (reS S b) T, symplOH (reS S b) T x y = symplOH S T (reW S T b x) (reW S T b y) := by
    intro x y
    unfold symplOH
    rw [hs]
  have hc := continuous_reW S T b
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hc, fun k L h1 h2 w => ?_⟩
  · have e := reW_ratW S T b γ
    rw [reF_apply, reF_apply, reW_add, hsH]
    erw [e]
    exact hf.quasi _ _
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap (reWHom S T b), hU.preimage hc, fun u hu h0 => ?_⟩
    rw [heisO_reF S T b ψ hs u f, h (reW S T b u) hu (reW_map_inf S T b h0)]
  · have := hf.smooth k ((reWHom S T b).comp L) (hc.comp h1) (fun t => reW_map_fin S T b (h2 t)) (reW S T b w)
    simp only [reF_apply, reW_add]
    exact this

end GlobalTheory.AdSpan.ReVec.ThetaCarry

end
