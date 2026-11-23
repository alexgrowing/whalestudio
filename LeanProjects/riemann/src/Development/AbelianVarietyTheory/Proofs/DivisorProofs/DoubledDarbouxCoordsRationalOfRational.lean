import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.DblSchr.ddr_rat : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro D S T JA JB ξ κ _ co h x
  obtain ⟨y₁, z₁, h₁⟩ := h (x.submatrix id finSumFinEquiv).toCols₁
  obtain ⟨y₂, z₂, h₂⟩ := h (x.submatrix id finSumFinEquiv).toCols₂
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e, Equiv.symm_symm]
  have e1 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₁ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁ := rfl
  have e2 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₂ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂ := rfl
  simp only [GlobalTheory.DblSchr.dblD, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, e1, e2, h₁, h₂]
  refine Prod.ext ?_ ?_
  · funext i; rcases i with i | i <;> rfl
  · funext i; rcases i with i | i <;> simp
