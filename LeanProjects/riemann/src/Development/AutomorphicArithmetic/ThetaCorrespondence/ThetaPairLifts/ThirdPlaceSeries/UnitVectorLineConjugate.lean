import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitVectorRowsConjugate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatchStatement

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
namespace GlobalTheory.MiTop.LineV
open GlobalTheory.PiTensorInner
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop.LineV
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop.LineV
end GlobalTheory.MiTop.LineV
namespace GlobalTheory.MiTop
theorem unit_vector_line_conjugate_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB v₀ v hv hn T hTm hT0 φ hφ hst
  obtain ⟨-, hθ, -, hM, -, -⟩ := _root_.GlobalTheory.T.bottom_hypothesis_matching_central_alt W hB
  have hMt : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
    have := hM 1 (one_mem _) (Subgroup.one_mem _)
    rwa [one_mul] at this
  obtain ⟨⟨j, hj, hjT⟩, -⟩ := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W)
    (show GA D (D.sp.Y 0) from W.Q.tS) v (by simp) hθ hB.gap hB.idE hMt hv
  obtain ⟨T', hT'⟩ := hj.2 ⟨star φ, hst⟩
  have h1 := hjT T'
  rw [hT'] at h1
  have he : evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX W.S.X]
      evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T'.1 (PiTensorProduct.tprod ℂ v)) := by
    filter_upwards [hφ, h1, Lp.coeFn_star φ] with x a1 a2 a3
    rw [← a1]
    have a4 := a3.symm.trans a2
    simpa using congrArg star a4
  exact LineV.line_of_eq hCR hθ hTm T'.2 v₀ v hn hT0 (LineV.eq_of_evS_ae W.S.X W.Q.instEq _ hTm T'.2 v₀ v he)
end GlobalTheory.MiTop
end
end
