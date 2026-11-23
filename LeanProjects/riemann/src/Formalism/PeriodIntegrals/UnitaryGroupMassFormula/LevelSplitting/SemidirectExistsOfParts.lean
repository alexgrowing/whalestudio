import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SubgroupLocallyCompactHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProdHaar

noncomputable section

namespace PI.LevelKSplit.W.ExS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.VolSemiDirect.W
open scoped TensorProduct

def SCAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], SecondCountableTopology (Af F)

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def SemiNHS : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    Semi (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)

def ConjNH : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ConjInv (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)

variable {F E σ M J}

theorem lcsc_HAf [FiniteDimensional F E] (hsc : SecondCountableTopology (Af F)) :
    LCSC (HA (Af F) σ J) := by
  haveI := hsc
  refine ⟨inferInstance, ?_, ?_, inferInstance⟩
  · haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
    let e := (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun
    have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : (Af F ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Af F) := ⟨e.toEquiv, hc1, hc2⟩
    haveI : SecondCountableTopology (Af F ⊗[F] E) := h.secondCountableTopology
    haveI h4 : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin M → Fin M → Af F ⊗[F] E))
    haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin M) (Af F ⊗[F] E)) :=
      Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
    show SecondCountableTopology ↥(HR (Af F) σ J)
    exact Topology.IsInducing.subtypeVal.secondCountableTopology
  · show T2Space ↥(HR (Af F) σ J)
    infer_instance

theorem existS_of [FiniteDimensional F E] (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x)
    (hPr : ProdHaarG) (hsc : SecondCountableTopology (Af F)) (hS : SemiNHS F E σ M J)
    (hCo : ConjNH F E σ M J) : ExistS F E σ M J := by
  intro r P T hP μN hN μH hH
  obtain ⟨hSc, hNc, hHc⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP
  obtain ⟨hLC, hSC, hT2, hTG⟩ := lcsc_HAf (σ := σ) (J := J) hsc
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hTG
  have hsub : ∀ K : Subgroup (HA (Af F) σ J), IsClosed (K : Set (HA (Af F) σ J)) → LCSC K := by
    intro K hK
    refine ⟨?_, ?_, ?_, inferInstance⟩
    · first
        | exact hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
        | exact hK.locallyCompactSpace
        | exact hK.closedEmbedding_subtypeVal.locallyCompactSpace
    · first
        | exact Topology.IsInducing.subtypeVal.secondCountableTopology
        | exact @Topology.IsInducing.secondCountableTopology _ _ _ _ hSC _ Topology.IsInducing.subtypeVal
    · first
        | exact inferInstance
        | exact Topology.IsEmbedding.subtypeVal.t2Space
  obtain ⟨μS, hμS, hprod⟩ := hPr (HA (Af F) σ J) _ _ _ (hS hJ hinv r P T hP) (hsub _ hSc)
    (hsub _ hNc) (hsub _ hHc) (hCo hJ hinv r P T hP) μN hN μH hH
  exact ⟨μS, hμS, hprod⟩

end Ext

def SemiNHSAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => SemiNHS F E σ M J

def ConjNHAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => ConjNH F E σ M J

theorem existSAll_of (hPr : ProdHaarG) (hsc : SCAf) (hS : SemiNHSAll) (hCo : ConjNHAll) :
    ExistSAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hσ.2.2.2 τ (σ x), hσ.2.2.2 τ x, star_star]
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact existS_of hJ hinv hPr (hsc F) (hS F E σ hσ M J hJ) (hCo F E σ hσ M J hJ)

end PI.LevelKSplit.W.ExS
