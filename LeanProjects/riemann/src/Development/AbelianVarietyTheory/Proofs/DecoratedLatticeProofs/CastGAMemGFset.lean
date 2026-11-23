import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem besGrp_iff_sA (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (g : GA D (D.sp.Y 0)) :
    g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := by
  have hS : besGrp B.d B.o = (Formalism.L2.SG.Pf.SAsub X u).comap (iotaX X h).toMonoidHom := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro n hn
        obtain ⟨h1, h2⟩ := (B.tieN n).1 hn
        exact ⟨fun v => (h1 v).1, Formalism.L2.SG.Pf.nfin_sfin X u h2⟩
      · intro g hg
        obtain ⟨h1, h2⟩ := (B.tieH g).1 hg
        exact ⟨hinf_le_sinf X u _ h1, Formalism.L2.SG.Pf.hfin_sfin X u ⟨_, h2⟩⟩
    · intro g hg
      have hg' : (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := hg
      obtain ⟨hg1, hg2⟩ := hg'
      obtain ⟨hi, hhi, ni, hni, ei⟩ := Formalism.L2.SG.Pf.Sinf.levi X u hg1
      obtain ⟨hf, nf, hnf, ef⟩ := Formalism.L2.SG.Closed.FinLeviC_holds D X u _ hg2
      have hgeq : g = (iotaX X h).symm (hi, (hf : X.B.I.Gf)) * (iotaX X h).symm (ni, nf) := by
        rw [← map_mul, (iotaX X h).eq_symm_apply]
        exact Prod.ext ei ef
      rw [hgeq]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
      · refine (B.tieH _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hhi, hf.2⟩
      · refine (B.tieN _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hni, hnf⟩
  rw [hS]; rfl

theorem besGrp_eq_sGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A),
    (∀ g, g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u) ∧
      ∀ g, g ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o ↔ iotaX X h g ∈ Srat X u := by
  intro D X h u ψ A B
  refine ⟨besGrp_iff_sA D X h u ψ A B, fun g => ?_⟩
  rw [Subgroup.mem_inf, besGrp_iff_sA D X h u ψ A B, Formalism.L2.SG.Pf.srat_eq, Subgroup.mem_inf,
    Formalism.MainNotions.LeviCoordinates.rr_mem_GF, Formalism.IndefR.RationalEmbedding.iota_rat]
  have e : iotaX X h g = Formalism.L2.SG.RowsJoinPinned.castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e, castGA_mem_GFset]
  rfl

end GlobalTheory.Core.Mi

end
