import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioOfLocalMatchingTowers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
open Finset GlobalTheory.FunObj.SqNum
namespace GlobalTheory.RowClaim
set_option maxHeartbeats 1600000 in
theorem twisted_local_factor_ratio_holds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ConstK →
    GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.TriEx → GlobalTheory.SqTop.Tower → RatioK := by
  intro hP hTA hLM hC hLN hTX hTW
  have hBF := _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hP hTA hLM hLN
  obtain ⟨c1, h1⟩ := hC
  obtain ⟨c5, h5⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hLN hTX) (GlobalTheory.SqTop.Model.gBig_and hTW hBF)
  refine ⟨max c1 c5, fun ε CF hCF => ?_⟩
  obtain ⟨x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C0, x5, g5⟩ := h5 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x5, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hi hsc => ?_⟩
  have hc := g1 D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hs ch hi hsc
  have hrec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hs.size, hs.host⟩
  have hL : R.toLevCh.Is A.μ0 := hs.core.lev
  intro hfield
  obtain ⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ := ch
  change sc = _ at hsc
  subst hsc
  obtain ⟨⟨hLN', hTX'⟩, hTW', hBF'⟩ := g5 C0 le_rfl D large₂ he (le_of_max_le_right hx) hrec T R.toLevCh A.μ0 hL G
  have hstd : IsStdChar D W.ψ (-1) := (hi.weil.ψ : W.ψ = _) ▸ hs.std
  exact fun i j t => sqRatio_mem_grid G A.μ0 W S.toGridChoice rm c hfield hc hi.const (fun i j => (hLN' i j).1)
    (hTX' W hstd) (hTW' W S.toGridChoice rm hstd hfield) (hBF' W hstd) i j t
end GlobalTheory.RowClaim
end
end
