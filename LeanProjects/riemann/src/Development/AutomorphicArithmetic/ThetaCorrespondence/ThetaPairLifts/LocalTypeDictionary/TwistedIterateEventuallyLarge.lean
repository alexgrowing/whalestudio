import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceValuationLinAtLarge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspStepOfLargeFlipRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EndCuspLeadingFormListed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidalStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
variable {D : D7}
section Lin
variable {ψ : AddChar (AF D.host.F) ℂ} {T₀ : HSp D}
end Lin
variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
variable (W : G.Weil) (M : Vol G) (t : T)
variable {W M t}
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun GlobalTheory.RowUnf GlobalTheory.RowVal
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
theorem twisted_iterate_eventually_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch := by
  intro hP hL
  obtain ⟨c0, h0⟩ := (_root_.GlobalTheory.T.flipRun_cusp_transition hL hP).and ((_root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList hP).and GlobalTheory.RowClaim.colFn_cont_left)
  refine ⟨c0, fun ε CF hC => ?_⟩
  obtain ⟨x0, hx⟩ := h0 ε CF hC
  refine ⟨x0, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R Fc hS ch hch hsc => ?_⟩
  obtain ⟨hstep, htop, hcol⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R Fc hS ch hch hsc
  choose ρ hρ hρ' using exists_rowMeas ch.G
  choose v hv using exists_vol_row ch.G
  refine ⟨ρ, fun j => (v j).μ, fun j hj => ⟨hρ j (mem_idx hj).2, (v j).haar⟩, ?_⟩
  intro t a τ hτ M hM P y
  obtain ⟨e, he, φm, hw, -⟩ := hτ
  have hu : GlobalTheory.Unf.IsContAut _ (colFn ch a) := ⟨(hcol a).2, (hcol a).1⟩
  have core : ∀ d ∈ τ.support,
      BplusConv ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) ∧
      NIter ρ (fun j => (v j).μ) (fun h => per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h) d.1 P.1 (colFn ch a) (formTop ch t y))
        (idx D) 1 (Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y))) := by
    intro d hd
    have h2 := hw d hd
    obtain ⟨-, h1, h3⟩ := pure_core hP.cuspRapidDecay hch.vol hM (hstep t M hM) he (φm d) d h2.1 h2.2 P (htop t y) hu
    refine ⟨GlobalTheory.RowBplus.bplusConv_col ch.W ch.M hch.vol ch.ξ (ch.col a) (col_mem ch a) _ h1.1.toIsAutFun, ?_⟩
    exact nIter_meas_congr ρ _ _ _ (fun j hj => hv j (mem_idx hj).1 (mem_idx hj).2.le t M hM)
      (nIter_conAt_of_colPer ch.G ch.W t hM (fockD ch.W t d.2 P.2) _ _ _ h3 ρ (fun j => (hρ' j t M hM).1)
        fun j => (hρ' j t M hM).2)
  have e1 : liftT ch.W M (oppPath t D.R.m) (oppTens ch.W t (Finsupp.single P 1) τ) (formTop ch t y) =
      ∑ d ∈ τ.support, τ d • liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y) := by
    rw [GlobalTheory.RowVal.liftT_oppTens, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
      one_smul]
  have e2 : lhs ch t M (Finsupp.single P 1) τ a y = ∑ d ∈ τ.support,
      τ d * Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) := by
    rw [lhs, e1, (bplus_sum_right ch.W ch.M (colFn ch a) τ.support _
      fun d hd => (bplus_smul_right ch.W ch.M (τ d) (core d hd).1).1).2]
    exact Finset.sum_congr rfl fun d hd => (bplus_smul_right ch.W ch.M _ (core d hd).1).2
  rw [e2]
  exact (niter_lin_congr _ _ _ ρ _ (idx D) 1).1 _ τ.support τ _ _ fun d hd => (core d hd).2
theorem twisted_iterate_eq_linear : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch ∧ LinAt ch :=
  fun hP hL => (_root_.GlobalTheory.RowChain.twisted_iterate_eventually_large hP hL).and (_root_.GlobalTheory.RowVal.placeValuation_linAt_large hP hL)
end GlobalTheory.RowChain
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_iterate_chain : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch ∧ LinAt ch := by
  first | exact @_root_.GlobalTheory.RowChain.twisted_iterate_eq_linear | exact _root_.GlobalTheory.RowChain.twisted_iterate_eq_linear | (intros; apply _root_.GlobalTheory.RowChain.twisted_iterate_eq_linear <;> assumption)
end
