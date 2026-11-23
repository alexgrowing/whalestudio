import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstanceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharactersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConj.exists_frame_symLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 → ∃ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔ κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0))) ∧ (κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = levChi (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) κ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp ψ0 hψ0
  classical
  obtain ⟨β, hβ, hred⟩ := GlobalTheory.T.exists_frame_reduction_eq_flagBasis_otherInstance R F X h hIs hGrp
  obtain ⟨ψ', a, hψ', hchi⟩ := GlobalTheory.T.conjCharacter_eq_prod_symmetricEdge_characters_alt R F X h hIs hGrp β hβ hred
  have hsc : ∀ PP ∈ R.Pg, ∃ d : Fin D.R.r → (kP PP)ˣ, ∀ u : GL (Fin D.R.r) (kP PP), u ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k →
      ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * u.val i j else 0) =
        ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) ((diagGL d)⁻¹ * u * diagGL d)) :=
    fun PP hP => GlobalTheory.T.exists_diagonal_conj_edgeSum_addChar_finiteField (κf := kP PP) ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal)
      D.R.rS D.R.k (ψ' PP) (ψ0 PP) (hψ' PP hP) (hψ0 PP hP) (a PP)
  choose! dd hdd using hsc
  obtain ⟨β₃, hβ₃, hSt, hconj⟩ := GlobalTheory.T.exists_frame_rescale_conj_reductions_diagonal (r_le_Y (D := D) 0) β _ hβ R.Pg dd
  refine ⟨β₃, hβ₃, fun κ => ?_⟩
  obtain ⟨hR1, hR2, hUA⟩ := GlobalTheory.T.instanceIota_readout_realTrivial_stabilizer_unitary X h β hβ κ
  obtain ⟨hL1, hL2⟩ := GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff R.toLevCh β₃ ψ0 κ
  have hgrp := GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hIs hGrp β hβ hred κ
  have key : κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔
      κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) := by
    refine Iff.trans ?_ hL1.symm
    show ((iotaX X h).toMulEquiv κ).1 = 1 ∧ ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ h2
      have hS := hR2.1 hK
      have hG' := (hgrp hK hS).1 h2
      refine ⟨hR1.1 h1, hUA, (hSt _).2 hS, fun PP hP => ?_⟩
      rw [hconj PP hP _ hS]
      exact (unipSym_conj_iff _ _ _ _).1 (hG' PP hP)
    · rintro ⟨h1, _, h3, h4⟩
      have hS : finE (Yc D 0) κ ∈ St β := (hSt _).1 h3
      have hK := hR2.2 hS
      refine ⟨hR1.2 h1, (hgrp hK hS).2 fun PP hP => ?_⟩
      have h5 := h4 PP hP
      rw [hconj PP hP _ hS] at h5
      exact (unipSym_conj_iff _ _ _ _).2 h5
  refine ⟨key, fun hk => ?_⟩
  obtain ⟨h1, _, h3, h4⟩ := hL1.1 hk
  have hS : finE (Yc D 0) κ ∈ St β := (hSt _).1 h3
  have hK := hR2.2 hS
  have hK2 : ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 := (key.2 hk).2
  rw [hL2 hk, hchi κ hS hK2]
  refine Finset.prod_congr rfl fun PP hP => ?_
  rw [hconj PP hP _ hS]
  exact hdd PP hP _ ((hgrp hK hS).1 hK2 PP hP)
