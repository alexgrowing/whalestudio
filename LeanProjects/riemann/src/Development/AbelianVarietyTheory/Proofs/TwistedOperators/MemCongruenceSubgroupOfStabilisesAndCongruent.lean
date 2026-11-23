import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CongAssemble

open Matrix

variable {D : D7}

theorem isIntM_of_smul_maps {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (s : Lev.EAf D) (M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (h : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, s • (M *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsIntM (s • ((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1)) := by
  intro i j
  have h1 := (hfr _).1 (h _ (GlobalTheory.FrameIdeal.col_mem_hatL hfr j)) i
  have e1 : (β⁻¹ : GL (Fin n) (Lev.EAf D)).1 *ᵥ (s • (M *ᵥ (β.1 *ᵥ Pi.single j 1))) =
      s • (((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1) *ᵥ Pi.single j 1) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, Matrix.mulVec_single_one] at h1
  simpa [Matrix.smul_apply] using h1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cong_assemble : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, PP.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  classical
  intro D V Λ hsd Z e hZe 𝔪 h𝔪 g hg hx
  obtain ⟨β, hfr⟩ := frame_exists_alt D.host.F D.host.E V.rank Λ hsd.1
  have hUA := GlobalTheory.LevSplit.finE_mem_UA V g
  have hγ : (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * (Lev.finE V g).1 * β.1 := by
    simp only [Units.val_mul]
  have hγi : ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * ((Lev.finE V g)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * β.1 := by
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have h1 : IsIntM (toEAf D e • (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγ]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').1
  have h2 : IsIntM (toEAf D e • ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγi]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').2.1
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral V Λ β hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, -, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element V (GlobalTheory.LevelNbhd.finPartG V g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC V g) hεε hεc
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame V β _ k (e + cA D e) hmt
  rw [GlobalTheory.SuppLevO.finE_finPartG] at hfk
  obtain ⟨hSt, -⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction V.rank β _ _ Z e hZe h1 h2 h3 h4 hfk
  have hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) g := fun PP hP => by
    rw [← GlobalTheory.SuppLevO.proj_finPartG V g]
    exact GlobalTheory.T.localProjection_eq_of_idempotent_patch V _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt
  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr k).1 hSt
  have hgSt : Lev.finE V g ∈ Formalism.L2.DIV.St β := by
    refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr g).2 fun v => ?_
    by_cases hv : ∃ PP ∈ Z, PP.under (𝓞 D.host.F) = v
    · obtain ⟨PP, hP, rfl⟩ := hv
      rw [← hcomp PP hP]
      exact hkloc _
    · push_neg at hv
      exact hg v hv
  have hfw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr hgSt
  have hbw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr (inv_mem hgSt)

  have h𝔪0 : 𝔪 ≠ ⊥ := by
    intro h0
    haveI := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.E
    exact Set.infinite_univ (Z.finite_toSet.subset fun PP _ => h𝔪 PP (by rw [h0]; exact bot_le))
  have hrad : (∏ PP ∈ Z, PP.asIdeal) ≤ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪0 (le_bot_iff.1 (h ▸ hJ))
    have hQ := h𝔪 ⟨J, hJp, hJ0⟩ hJ
    calc (∏ PP ∈ Z, PP.asIdeal) = (∏ PP ∈ Z.erase ⟨J, hJp, hJ0⟩, PP.asIdeal) * J := (Finset.prod_erase_mul _ _ hQ).symm
      _ ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right | exact Ideal.mul_le_left'
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg 𝔪 (IsNoetherian.noetherian _)
  have hle : (∏ PP ∈ Z, PP.asIdeal ^ N) ≤ 𝔪 := by
    rw [Finset.prod_pow]
    exact (Ideal.pow_right_mono hrad N).trans hN
  obtain ⟨t, ht, htv⟩ := (GlobalTheory.IdemSumIdeal.isIdemSum_props e Z (fun _ => N) hZe).2.2
  refine GlobalTheory.ChiGrid.mem_congLev.2 ⟨hUA, fun x => ⟨fun hx' => hfw x hx', fun hx' => ?_⟩, fun x hx' => ?_⟩
  · have := hbw _ hx'
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  · have hw : (Lev.finE V g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := Submodule.sub_mem _ (hfw x hx') hx'
    have e1 : (Lev.finE V g).1 *ᵥ x - x = toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) +
        (1 - toEAf D e) • ((Lev.finE V g).1 *ᵥ x - x) := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [e1]
    refine Submodule.add_mem _ (hx x hx').2.2 ?_
    rw [← htv]
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) (GlobalTheory.FrameIdeal.idS_smul_mem_hatL Λ ht hw)

end GlobalTheory.CongAssemble
