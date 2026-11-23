import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFrameChangeMemIntegralGLAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameReductionEqOneOfFrameMatrixCongruentOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixComponentSubOneEqZeroOffIdempotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace

theorem datP_ne_zero_unpack {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ea : AE D)
    (y : WO (Vc D i) (Wc D i)) (h : datP R i t ea y ≠ 0) :
    IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) ∧
    (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) ∧
    (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) := by
  unfold datP at h
  split_ifs at h with hc
  · refine ⟨hc.2, fun PP hPP => ?_, fun PP hPP => ?_⟩
    · have hK := left_ne_zero_of_mul h
      unfold omegaK at hK
      split_ifs at hK with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hK
    · have hQ := right_ne_zero_of_mul h
      unfold omegaQ at hQ
      split_ifs at hQ with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hQ
  · exact absurd rfl h

theorem disj_supp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ea : AE D), IsIdemSum ea (R.Pg ∪ R.Q t) → ∀ (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → ∀ x x' : WO (Vc D i) (Wc D i), (∀ a b, f * x a b = f * x' a b) → datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x) ≠ 0 → datP R i t ea x' ≠ 0 → False := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hFP i t ea hea P hP e f hpe k hk hkn x x' hxx h1 h2
  apply hkn
  have hPS : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨heP, hfe, hcf, hinf, hcP⟩ := GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split D P e f ea (R.Pg ∪ R.Q t) hpe hea hPS
  obtain ⟨hI1, hK1, hQ1⟩ := datP_ne_zero_unpack R i t ea _ h1
  obtain ⟨hI2, hK2, hQ2⟩ := datP_ne_zero_unpack R i t ea _ h2
  have hY := GlobalTheory.T.frameMapAdjoint_translate_inv_eq_mul_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) k x
  have hid := GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split D (Vc D i) (Wc D i) (R.βV i) (R.βW i) f hcf k hk x x' hxx
  rw [← hY] at hid

  have he1 := GlobalTheory.StdFrames.cpt_of_isIdemAt heP
  have hcPP : GlobalTheory.IdemSupport.cP P ≠ P := hcP P hPS
  have hfP : GlobalTheory.StdFrames.cpt P (toEAf D f) = 1 := by
    rw [hfe, RingHom.map_add, GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add, he1.1,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ hcPP), add_zero]
  have hfoff : ∀ PP ∈ R.Pg, PP ≠ P → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 := by
    intro PP hPP hne
    rw [hfe, RingHom.map_add, GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add, he1.2 _ hne,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ (hcP PP (Finset.mem_union_left _ hPP))), add_zero]
  have hu : ∀ (y : WO (Vc D i) (Wc D i)), (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) →
      (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) →
      IsUnit (topL (Wc D i).rank (redM P (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det := by
    intro y hK hQ
    rcases hP with hP | hP
    · rw [hK P hP, Matrix.det_one]; exact isUnit_one
    · exact hQ P hP
  obtain ⟨hint, hdet, hone⟩ := GlobalTheory.T.localFrameChange_mem_integralGL_at_place D P _ _ _ _ _ _ hfP hid hI2 hI1 (hu _ hK2 hQ2) (hu _ hK1 hQ1)
  have hSt := GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport D (Wc D i) (R.βW i) (R.ΛW i) (hL.lev.βW i) e f P heP hfe hcPP k hk hint hdet
  have hred : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → redFn (R.βW i) PP (finE (Wc D i) k) = 1 := by
    rintro PP (hPP | hPP)
    · change PP ∈ R.Pg at hPP
      refine GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one D (Wc D i) (R.βW i) k PP hSt ?_
      by_cases hPe : PP = P
      · subst hPe
        exact hone (hK2 PP hPP) (hK1 PP hPP)
      · intro a b
        rw [GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent D (Wc D i) (R.βW i) f k PP hk (hfoff PP hPP hPe) a b, map_zero]
        exact zero_lt_one
    · exact absurd hPP (Finset.notMem_empty _)
  exact ⟨GlobalTheory.IdemSupport.mem_GfC_of_suppF (Wc D i) hinf hk,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv) _ (GlobalTheory.LevSplit.finE_mem_UA _ k) hSt hred⟩

end GlobalTheory.BadPlace

end
