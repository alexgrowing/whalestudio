import Formalism.LocalToGlobal.NormalizedHeckeFactors.BaseRowsEqRecordRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
namespace Formalism.L2.N.ExtNRows3
open Formalism.L2.N.ExtNRows
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
section Pin
variable (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
include hp hL h in
open Classical in
theorem base_rows_eq_record_rows_alt : P.S0.D = D.what₂.D0 := by
  obtain ⟨cOf, -, -, h3⟩ := hL
  have e1 := sum_finrank P.S0.Ep (Ep_decomp P h).1 (Ep_decomp P h).2
  rw [Module.finrank_fin_fun] at e1
  have e2 : ∑ c, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = ∑ σ, D.what₂.nRows0 σ :=
    Finset.sum_fiberwise _ _ _
  have e3 : ∑ σ, D.what₂.nRows0 σ = D.what₂.D0 := by
    unfold Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  rw [← e1, ← e3, ← e2]
  exact Finset.sum_congr rfl fun c _ => (h3 c).symm
include hp hL h in
theorem finrank_Mj_eq_D0 : ∀ j, 1 ≤ j → j ≤ D.R.m → finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := finrank_Mj_eq_dW P ⟨k, by omega⟩
  rw [dW_eq_D P h, _root_.Formalism.L2.N.ExtNRows3.base_rows_eq_record_rows_alt T P hp hL h] at this
  exact this
end Pin
theorem thetaT_injective_and_finrank_Zj_eq_D0_of_surjective (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (hp : _root_.Formalism.L2.Rows.RowSideDeterminedAlt T P) (hL : RowsHoldLam3 P) (h : RowsHold0_3 P)
    (hR : Formalism.L2.DIV.DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (i : Fin D.R.m) (t : P.T)
    (hl : Function.Surjective (lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec) :
    Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) ∧
      finrank ℂ (D.what₂.Zj (P.I.tup t) ((i : ℕ) + 1)) = D.what₂.D0 := by
  have hi : Function.Injective (D.what₂.thetaT (P.I.tup t) ((i : ℕ) + 1)) :=
    adjoint_injective _ (thetaP_surj P h hR i t hl)
  refine ⟨hi, ?_⟩
  unfold Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj hi]
  exact _root_.Formalism.L2.N.ExtNRows3.finrank_Mj_eq_D0 T P hp hL h _ (Nat.succ_le_succ (Nat.zero_le _)) i.2
end Formalism.L2.N.ExtNRows3
end
end
