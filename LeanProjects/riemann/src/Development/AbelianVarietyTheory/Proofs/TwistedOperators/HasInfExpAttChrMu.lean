import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowRealEq

variable {D : D7} {T : Type} {L : LevCh D T}

theorem hasInfExp_attChr_mu {μ0 : T} (hL : L.Is μ0) (t : T) {j : ℕ} (hj : j < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) τ
      (-(D.hc τ).e ⟨j, hj⟩ - if Odd n then 1 / 2 else 0) := by
  have h0 := GlobalTheory.ColKer.mu_exp hL t j hj τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem realEqAt : Big fun ch => RealEqAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  have hL := hS.core.lev
  intro t t' j hj
  refine ⟨fun a ha b hb f hf => ?_, fun a ha b hb f hf => ?_⟩
  · exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _
      (ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega)) (ch.W.om_is (.top t' j) (show j + 1 ≤ D.R.m by omega))
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩)
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩) a ha b hb f hf
  · exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _
      (ch.W.om_is (.mu t D.R.m j) (show D.R.m ≤ D.R.m ∧ j + 1 ≤ D.R.m by omega))
      (ch.W.om_is (.mu t' D.R.m j) (show D.R.m ≤ D.R.m ∧ j + 1 ≤ D.R.m by omega))
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩)
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩) a ha b hb f hf

end GlobalTheory.RowRealEq
