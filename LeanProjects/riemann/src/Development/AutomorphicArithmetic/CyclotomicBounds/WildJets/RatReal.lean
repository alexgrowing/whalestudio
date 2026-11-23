import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.ratReal :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (r : FinPt G X)
      (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E), GlobalTheory.RatMoveJets.RatCoord _ (fr X) r U →
      ∃ γ ∈ GQ (G.V X), ∃ k ∈ GinfC (G.V X), (∀ x : FinPt G X, ((r * x : FinPt G X) : GA D (G.V X)) = γ * ((x : GA D (G.V X)) * k)) ∧
        GlobalTheory.DefStep.realAct W.θ fr X k⁻¹ = rhoVr (tauE D) (wt G X) (Unitary.toUnits U) := by
  intro D T L sc G W fr X r U h
  obtain ⟨γ, hγ, hf, hm⟩ := h
  have hk : γ⁻¹ * (r : GA D (G.V X)) ∈ GinfC (G.V X) := by
    show finHom (G.V X) (γ⁻¹ * (r : GA D (G.V X))) = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  refine ⟨γ, hγ, γ⁻¹ * (r : GA D (G.V X)), hk, fun x => ?_, ?_⟩
  · have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC (G.V X) hk x.2
    rw [← hc, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rfl
  · have hrat : Bridge.IsRatMat (G.V X) ⟨γ, hγ⟩ (fr X * Unitary.toUnits U * (fr X)⁻¹) := Units.ext hm
    have hin : GlobalTheory.DefStep.realIn W.θ fr X γ = embGL (tauE D) (Unitary.toUnits U) := by
      funext τ
      have h1 := GlobalTheory.CoefModel.realGL_rat W.θ_is (G.V X) ⟨γ, hγ⟩ _ hrat τ
      have h2 : GlobalTheory.DefStep.realIn W.θ fr X γ τ = (GlobalTheory.DefStep.frGL fr X τ)⁻¹ *
          GlobalTheory.CoefModel.realGL W.θ (G.V X) γ τ * GlobalTheory.DefStep.frGL fr X τ := by
        simp [GlobalTheory.DefStep.realIn]
      rw [h2, h1, map_mul, map_mul, map_inv, GlobalTheory.DefStep.frGL]
      show _ = Formalism.UG.bc (tauE D τ) (Unitary.toUnits U)
      group
    rw [_root_.mul_inv_rev, inv_inv, map_mul,
      GlobalTheory.DefStep.realAct_fin W.θ fr X (inv_mem r.2), one_mul, GlobalTheory.DefStep.realAct, MonoidHom.comp_apply,
      MonoidHom.comp_apply, hin]
    rfl
