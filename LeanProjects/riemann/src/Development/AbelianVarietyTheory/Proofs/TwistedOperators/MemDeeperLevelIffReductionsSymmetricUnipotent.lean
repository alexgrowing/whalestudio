import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteMatrixIotaEqFinitePartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueIdempotentConjAtLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DivisibilityTypeProductReadLevelPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencesReductionMemSymmetricUnipotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem GlobalTheory.SeeConjRead.mem_deeperLevel_iff_reductions_symmetricUnipotent : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → finE (Yc D 0) κ ∈ St β → (((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ ∀ PP ∈ R.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred κ hK hS
  classical
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hFH : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew :=
    ⟨vectorsInLattice, gramIntegral, formsAtZero, weightVectorsIntegral, ew_orth, bw_w, bwd_w, bw_dual, latticeSpan⟩
  obtain ⟨hgP, hZ⟩ := GlobalTheory.T.divisibility_typeProduct_read_levelPlaces R F hIs hGrp
  have hL : (II D).L = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
    ext x
    refine (Formalism.L2.SG.InstExistsPf.mem_Lv D x).trans ?_
    simp only [Formalism.L2.Herm.crdLat, Formalism.L2.Herm.crd]
    constructor
    · intro hx
      refine ⟨(VS D).frame.equivFun.symm x, ?_, (VS D).frame.equivFun.apply_symm_apply x⟩
      have e := Module.Basis.equivFun_symm_apply (VS D).frame x
      rw [← e] at hx
      exact hx
    · rintro ⟨y, hy, hyx⟩
      change (VS D).frame.equivFun y = x at hyx
      rw [← hyx, (VS D).frame.sum_equivFun y]
      exact hy
  have hβ' : IsFrame β (II D).L := by rw [hL]; exact hβ
  have hloc : ∀ PP ∈ R.Pg, ∃ w : Bool,
      LocAt (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew β PP w := by
    intro PP hP
    obtain ⟨h1, h2, hA1, hA0⟩ := GlobalTheory.T.residue_idempotent_conj_at_levelPlace (D.host.g 0 * D.host.g 1) ew ew_idem ew_orth ew_int ew_full PP (hgP PP hP)
    have hr : RedIs β PP (if GlobalTheory.StdFrames.cpt PP ew = 1 then
        flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bw z0
      else flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (fun i => bwd (Fin.rev i)) z0) := hred PP hP
    by_cases hc : GlobalTheory.StdFrames.cpt PP ew = 1
    · rw [if_pos hc] at hr
      exact ⟨true, hgP PP hP, fun _ => by simpa using (hA1 hc).1, fun _ => by simpa using (hA1 hc).2, hr⟩
    · rw [if_neg hc] at hr
      exact ⟨false, hgP PP hP, fun _ => by simpa using (hA0 hc).1, fun _ => by simpa using (hA0 hc).2, hr⟩
  have hxM : (II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := GlobalTheory.T.finiteMatrix_iota_eq_finitePart κ
  show _ ∧ _ ↔ _
  constructor
  · rintro ⟨-, hc⟩ PP hP
    obtain ⟨w, hw⟩ := hloc PP hP
    exact GlobalTheory.T.congruences_reduction_mem_symmetricUnipotent _ e0 f0 z0 bw bwd ew hFH β PP w hβ' hw _ (finE (Yc D 0) κ) hK hxM hS hc
  · intro hu
    exact ⟨hK, GlobalTheory.T.local_frame_hermitian_ideal _ e0 f0 z0 bw bwd ew hFH β R.Pg hβ' hloc hZ _ (finE (Yc D 0) κ) hK hxM hS hu⟩
