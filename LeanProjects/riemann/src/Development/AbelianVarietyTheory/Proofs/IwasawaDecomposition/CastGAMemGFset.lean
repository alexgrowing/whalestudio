import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFund

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.SchurMove

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem schur_iotaX : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : Formalism.IndefR.Datum.InfFam D) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), SchurAll D → (D.sp.Y 0).SigOK → IsInfFam θ → E ≤ Mult θ M J χ → (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t)) * T' v' ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) := by
  intro D S M E St h θ J χ t hS hsig hθ hE T hT T' hT'
  haveI := St.B.haar
  haveI := St.B.sf
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ Formalism.L2.SG.RowsJoinPinned.iotaX St h g ∈ St.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact castGA_mem_GFset _ _
  exact GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => hS _ hsig S θ M J χ μ 𝓕) hθ St.B.I St.B.μf
    St.B.fund St.B.fund_spec (Formalism.L2.SG.RowsJoinPinned.iotaX St h) hι t T (hE hT) T' (hE hT')

end GlobalTheory.Mem.SJ.SchurMove
