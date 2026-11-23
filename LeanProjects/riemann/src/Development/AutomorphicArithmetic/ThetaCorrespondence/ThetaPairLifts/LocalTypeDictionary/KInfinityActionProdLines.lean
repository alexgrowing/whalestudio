import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianListStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.KInfLines
variable {D : D7}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7} {W : HSp D} {V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7} {W : HSp D} {V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}
theorem kInfinity_prod_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  intro _ D θ W Bs V r s hJ hθ _ hV k hk
  obtain rfl := Eqv.eq_thetaC D hθ
  choose C hC using cartan_data hJ Bs hV hk
  choose Z hZ using fun t => exists_log_of_cartan (GlobalTheory.SmoothForms.RealPts.gramAt_herm W t) (hC t).1
    (unitFam_gsOf hJ k t) (hC t).2.1
  refine ⟨Finset.univ.toList.map fun t => (t, Z t), ?_, prod_eq hJ hk.1 Z fun t => ⟨(hZ t).1, (hZ t).2.2⟩⟩
  intro q hq
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq
  exact ⟨(hZ t).1, line_mem hJ Bs C (fun t => (hC t).2.2) (hZ t).1 (hZ t).2.1⟩
end GlobalTheory.KInfLines
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kInfinity_action_prod_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  first | exact @_root_.GlobalTheory.KInfLines.kInfinity_prod_lines | exact _root_.GlobalTheory.KInfLines.kInfinity_prod_lines | (intros; apply _root_.GlobalTheory.KInfLines.kInfinity_prod_lines <;> assumption)
end
