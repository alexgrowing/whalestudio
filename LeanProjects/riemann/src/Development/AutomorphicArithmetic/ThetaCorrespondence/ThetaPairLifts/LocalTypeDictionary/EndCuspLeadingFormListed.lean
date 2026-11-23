import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopFormsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.EndCusp
open Formalism.IndefR.Mult Matrix
variable {D : D7}
end GlobalTheory.EndCusp
namespace GlobalTheory.EndCusp
open Formalism.IndefR.Mult Matrix
variable {D : D7}
end GlobalTheory.EndCusp
namespace GlobalTheory.EndCusp
open Formalism.IndefR.Mult Matrix
variable {D : D7}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.EndCusp
namespace GlobalTheory.EndCusp
theorem leadingForm_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hm := hS.core.models
  obtain ⟨h1, h2, h3⟩ := formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  obtain ⟨k1, k2, k3⟩ := props_cast R.θ (fun τ => Node.par D ch.sc.cGap (.grid 0 D.R.m) τ) (columnBlock R.toLevCh D.R.m)
    (colY_m R.toLevCh) (ch.cv.formX t y) h1 h2 (fun τ => by
      rw [show Node.par D ch.sc.cGap (.grid 0 D.R.m) τ = (Ptw D).Dpar D.R.m τ from parV_zero D _ le_rfl τ]
      exact h3 τ)
  rw [hθ]
  exact ⟨k1, k2, k3⟩
end GlobalTheory.EndCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endCusp_leadingForm_listed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @_root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList | exact _root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList | (intros; apply _root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList <;> assumption)
end
