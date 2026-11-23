import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThK.LocalOps
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
theorem theta_kernel_local_operators_act (_hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : GlobalTheory.ThK.ActsEx := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  have hex : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ :=
    fun x hx1 hx2 φ hφ => acts_exists hP v x hx1 hx2 φ hφ
  refine ⟨fun g hg h hh φ hφ => ?_, fun u hu φ hφ => ?_, GlobalTheory.T.weilRep_smooth_at_finitePlace B X W M χX χW om r s r' s' hP v hex⟩
  · obtain ⟨φ₁, h1, h2⟩ := hex (g, h) hg hh φ hφ
    exact ⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 h2⟩
  · refine ⟨GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ,
      ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hP.base.std.1 v _ φ hφ, GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ⟩,
      fun φ₂ hφ₂ => acts_unique v _ hφ hφ₂.2 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)⟩
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
namespace GlobalTheory.ThK.LocalOps
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.ThK.LocalOps
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_local_operator_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.ThK.ActsEx := by
  first | exact @_root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | exact _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act | (intros; apply _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act <;> assumption)
end
