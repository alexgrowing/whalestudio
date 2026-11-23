import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInvStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatchStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LocSuppTw

variable {D : D7}

theorem datum_specQ (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D)
    (x : WO S T)
    (hx : (if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) *
      omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) ≠ 0) :
    IsIntM (frMapO S T βS βT x) ∧
    (∀ PP ∈ L.Pg, IsUnit (topL S.rank (redM PP (frMapO S T βS βT x))).det) ∧
    ∃ a : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1),
      (∀ PP : ↥L.Pg, ((a PP : GL (Fin S.rank) (kP PP.1)) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)) =
        topL S.rank (redM PP.1 (frMapO S T βS βT x))) ∧
      (∀ PP : ↥L.Pg, a PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (a PP)) ∈ L.P.H := by
  by_cases hc : IsHalf e x ∧ IsIntM (frMapO S T βS βT x)
  · rw [if_pos hc] at hx
    have hG := left_ne_zero_of_mul hx
    unfold omegaG at hG
    split_ifs at hG with hd
    · refine ⟨hc.2, fun PP hPP => ?_, hd.2⟩
      obtain ⟨a, ha, -, -⟩ := hd.2
      rw [← ha ⟨PP, hPP⟩]
      exact Matrix.isUnits_det_units (a ⟨PP, hPP⟩)
    · exact absurd rfl hG
  · rw [if_neg hc] at hx
    exact absurd rfl hx

theorem idemSum_left {e : AE D} {P Q : Finset (Pl D.host.E)} (h : IsIdemSum e (P ∪ Q)) :
    ∃ e₁ : AE D, IsIdemSum e₁ P := by
  obtain ⟨e₁, h₁⟩ := GlobalTheory.ExportSeries.SplitSet.mono ⟨e, h⟩ Finset.subset_union_left
  exact ⟨e₁, h₁⟩

theorem isIntM_smul' {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) : IsIntM (c • N) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem hc (hN i j)

theorem redM_smul_of_res {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Pl D.host.E)
    (h1 : Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = 1) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    redM PP (c • N) = redM PP N := by
  ext i j
  have h2 : (c • N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := isIntM_smul' hc hN i j
  have hsub : (⟨(c • N) i j, h2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨c, hc⟩ * ⟨N i j, hN i j⟩ :=
    Subtype.ext (by simp [Matrix.smul_apply])
  unfold redM
  rw [dif_pos h2, dif_pos (hN i j), hsub, map_mul, h1, one_mul]

end GlobalTheory.LocSuppTw

namespace GlobalTheory.LocSuppTw

theorem smul_mul_gen {R : Type} [CommRing R] {a b c : ℕ} (f : R) (A : Matrix (Fin a) (Fin b) R)
    (G : Matrix (Fin b) (Fin c) R) : (f • A) * G = f • (A * G) := by
  ext i k
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem tri_of_mul_eq {κ : Type} [Field κ] {n r t : ℕ} (hr : r ≤ n) {a b R : GL (Fin n) κ} (h : b * R = a)
    (ha : a ∈ blockTri (blkOf r t)) (hb : b ∈ blockTri (blkOf r t)) (ha1 : upperLeftBlock hr a = 1) (hb1 : upperLeftBlock hr b = 1) :
    R ∈ blockTri (blkOf r t) ∧ upperLeftBlock hr R = 1 := by
  have hR : R = b⁻¹ * a := by rw [← h, inv_mul_cancel_left]
  have hmem : R ∈ blockTri (blkOf r t) := by
    rw [hR]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha
  refine ⟨hmem, ?_⟩
  have hle := blockTri_blkOf_le (κ := κ) (n := n) r t
  have ha2 := hle ha
  have hb2 := hle hb
  unfold upperLeftBlock at ha1 hb1 ⊢
  rw [hR, extendMatrixByIdentityAlongIndices_mul (blkR hr) (Subgroup.inv_mem _ hb2) ha2, extendOne_inv (blkR hr) hb2, ha1, hb1, inv_one, one_mul]

set_option maxHeartbeats 1000000 in

theorem finE_gAt_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) → PP' = PP) → Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) ∈ Formalism.L2.DIV.St βS ∧ Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g))) = 1 := by
  intro D S T ΛS βS βT L χ ξ e hSD hFr hST hId hH g x hx hgx PP hPP _
  have hHalf : IsHalf e x := by
    by_contra hn
    exact hx (if_neg fun h => hn h.1)
  obtain ⟨hI1, hU1, a, ha, haT, haH⟩ := datum_specQ S T βS βT L χ ξ L.Q e x hx
  obtain ⟨hI2, hU2, a', ha', ha'T, ha'H⟩ := datum_specQ S T βS βT L χ ξ L.Q e (actO S T g 1 x) hgx

  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin S.rank) (Lev.EAf D), γ = βS⁻¹ * Lev.finE S g * βS := ⟨_, rfl⟩
  have hact : frMapO S T βS βT (actO S T g 1 x) = frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
    rw [hγ]
    exact GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x

  obtain ⟨e₁, h₁⟩ := idemSum_left hId
  obtain ⟨hc, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum h₁
  have hcc : toEAf D e₁ * toEAf D e₁ = toEAf D e₁ := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self h₁]
  have hmul : toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val =
      toEAf D e₁ • (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := smul_mul_gen _ _ _
  have hI2' : IsIntM (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [← hact]
    exact hI2
  have hu1 : IsIntM (toEAf D e₁ • frMapO S T βS βT x) := isIntM_smul' hc hI1
  have hu1g : IsIntM (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [hmul]
    exact isIntM_smul' hc hI2'
  have hsupp : ∀ i j, toEAf D e₁ * (toEAf D e₁ • frMapO S T βS βT x) i j = (toEAf D e₁ • frMapO S T βS βT x) i j := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
  have hred1 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x) = redM PP (frMapO S T βS βT x) :=
    fun PP hP => redM_smul_of_res hc PP (hres PP hP) hI1
  have hred2 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) =
      redM PP (frMapO S T βS βT (actO S T g 1 x)) := by
    intro PP hP
    rw [hmul, hact]
    exact redM_smul_of_res hc PP (hres PP hP) hI2'

  obtain ⟨hγ1, hγ2, htop⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions (D := D) T.rank S.rank hST L.Pg e₁ h₁ (toEAf D e₁ • frMapO S T βS βT x) γ
    hu1 hu1g hsupp (fun PP hP => by rw [hred1 PP hP]; exact hU1 PP hP) (fun PP hP => by rw [hred2 PP hP]; exact hU2 PP hP)
  obtain ⟨hγ3, hγ4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hSD hFr (Lev.finE S g) (GlobalTheory.LevSplit.finE_mem_UA S g) γ hγ e₁ hγ1 hγ2

  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed L.Pg e₁ h₁
  obtain ⟨k, -, hk⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e₁ + cA D e₁)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hkE := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS (GlobalTheory.LevelNbhd.finPartG S g) k (e₁ + cA D e₁) hk
  rw [GlobalTheory.SuppLevO.finE_finPartG, ← hγ] at hkE
  obtain ⟨hkSt, hkred⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS γ (Lev.finE S k) L.Pg e₁ h₁ hγ1 hγ2 hγ3 hγ4 hkE
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g :=
    (GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ (GlobalTheory.LevelNbhd.finPartG S g) k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one L.Pg e₁ h₁ PP hPP) hk).trans
      (GlobalTheory.SuppLevO.proj_finPartG S g _)
  have hyv : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) (gAt S (.inl (PP.under (𝓞 D.host.F))) g) =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g :=
    GlobalTheory.AdelicU.proj_emb_self (σ := D.sp.cm.sig) (J := S.gram) _ _

  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hFr k).mp hkSt
  have hyS : Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) ∈ Formalism.L2.DIV.St βS := by
    rw [GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hFr]
    intro w
    by_cases hw : w = PP.under (𝓞 D.host.F)
    · subst hw
      rw [hyv, ← hpk]
      exact hkloc _
    · show GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram w (GlobalTheory.AdelicU.emb D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F))
        (GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g)) ∈ _
      rw [GlobalTheory.AdelicU.proj_emb_ne (h := hw)]
      exact one_mem _

  have hk' : Lev.finE S k = Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) *
      Lev.finE S ((gAt S (.inl (PP.under (𝓞 D.host.F))) g)⁻¹ * k) := by
    rw [map_mul, map_inv, mul_inv_cancel_left]
  have hk'S : Lev.finE S ((gAt S (.inl (PP.under (𝓞 D.host.F))) g)⁻¹ * k) ∈ Formalism.L2.DIV.St βS := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hkSt
  have hproj1 : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F))
      ((gAt S (.inl (PP.under (𝓞 D.host.F))) g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hpk, hyv, inv_mul_cancel]
  have hR : Formalism.L2.DIV.redFn βS PP (Lev.finE S k) =
      Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g)) := by
    rw [hk', Formalism.L2.DIV.redFn_mul hyS hk'S, GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS _ PP hk'S hproj1, mul_one]

  have hmulGL : a' ⟨PP, hPP⟩ * Formalism.L2.DIV.redFn βS PP (Lev.finE S k) = a ⟨PP, hPP⟩ := by
    apply Units.ext
    rw [Units.val_mul, hkred PP hPP, ha' ⟨PP, hPP⟩, ha ⟨PP, hPP⟩]
    have htopPP := htop PP hPP
    rw [hred2 PP hPP, hred1 PP hPP] at htopPP
    exact htopPP
  have hrb : ∀ b : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1), (fun PP => upperLeftBlock L.hr (b PP)) ∈ L.P.H →
      ∀ PP, upperLeftBlock L.hr (b PP) = 1 := by
    intro b hb PP'
    rw [hH, Subgroup.mem_bot] at hb
    exact congrFun hb PP'
  obtain ⟨h1, h2⟩ := tri_of_mul_eq L.hr hmulGL (haT _) (ha'T _) (hrb a haH _) (hrb a' ha'H _)
  rw [← hR]
  exact ⟨hyS, h1, h2⟩

end GlobalTheory.LocSuppTw
