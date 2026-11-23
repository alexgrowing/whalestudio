import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFiniteOpenSubgroups
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finite_openSubgroups : ∀ (D : D7) (a b : ℕ) (JA : Matrix (Fin a) (Fin a) D.host.E) (JB : Matrix (Fin b) (Fin b) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    ∀ p0 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p
          (co.e.symm (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x', GlobalTheory.WeilCont.adeleJoin D.host.F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) := by
  first | exact @GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D | exact GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D | (intros; apply GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D <;> assumption)
