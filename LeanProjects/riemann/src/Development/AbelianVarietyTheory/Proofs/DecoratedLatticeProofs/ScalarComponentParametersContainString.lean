import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpsTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorsLatticeVacuaOffFiniteSet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.LiftParams

theorem param_of_sysParam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s y, IsEigV R i t h s y → ∀ l : (R.cV i).W →ₗ[ℂ] ℂ, (fun g => l (R.extV i t y g)) ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B → GlobalTheory.LFun.IsParamFunV (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (fun g => l (R.extV i t y g)) B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _hF i t h hh s y hy l hl B hB
  have hC := hG.core
  have h1 := hC.lev.βV i
  unfold IsSDFrame at h1
  obtain ⟨n, hBase⟩ := h1
  have hBase1 : IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1 := by
    simpa only [one_pow] using hBase
  have hfm := Eq.le (hC.models.HV i t).right.left (LinearMap.mem_range_self (R.HV i t).e y)
  have hc := hC.models.cV i
  have hS : ∀ PP : Pl D.host.E, PP ∈ (flag1L (R.datVt i t)).Pg ∨ PP ∈ (flag1L (R.datVt i t)).Q →
      HeightOneSpectrum.under (𝓞 ↥D.host.F) PP ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t :=
    fun _ hPP => GlobalTheory.DownLift.Params.under_mem_badPl R t hPP
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D (Vc D i) (R.βV i) (R.ΛV i) (flag1L (R.datVt i t))
    (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) hBase1 hS).1

  have hfix : ∀ P : Pl D.host.E, GlobalTheory.Hk3.Good R t P → ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ g,
      l ((R.extV i t) y (g * k)) = l ((R.extV i t) y g) := by
    intro P hP k hk g
    have hlo := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) 1 (flag1L (R.datVt i t)) hBase1 P
      (GlobalTheory.DefLiftHecke.one_pow_notMem P 0) (fun PP hPP => hP PP hPP)).1 k hk
    exact congrArg l (GlobalTheory.DefLiftHecke.ext_level (R.cV i) hc hfm hlo.1 hlo.2 g)
  refine ((GlobalTheory.LFun.param_iff_sysParam D (Vc D i) (↑(levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))))
    (levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) s B hsph).1
    (fun g => l ((R.extV i t) y g)) hl ?_ ?_).2 hB
  · intro v hv k hk g
    have hw0 : ∃ w : HeightOneSpectrum (𝓞 D.host.E), HeightOneSpectrum.under (𝓞 ↥D.host.F) w = v := GlobalTheory.ChainOnto.VacOffS.exists_under v
    obtain ⟨w, hw⟩ := hw0
    have hgood : GlobalTheory.Hk3.Good R t w := (GlobalTheory.DownLift.Params.good_iff R t w).2 (by rw [hw]; exact hv)
    have hm : (GlobalTheory.AdelicU.emb _ (HSpace.gram (Vc D i)) v) k ∈ GlobalTheory.Hk3.hyp (Vc D i) w := (GlobalTheory.HypDict.mem_hyp_iff_embV D v w hw (Vc D i) _).2 ⟨k, hk, rfl⟩
    exact hfix w hgood _ hm g
  · intro P d Rr hR
    have hoff : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) P := by
      obtain ⟨_, _, _, _, hoff, _⟩ := hR
      exact hoff
    have hgood : GlobalTheory.Hk3.Good R t P := (GlobalTheory.Hk3.OpsRowsTuple.offS_badPl_iff R t P).1 hoff
    have hsp : GlobalTheory.Hk3.SphOp (Vc D i) P d Rr :=
      (((GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) 1 (flag1L (R.datVt i t)) hBase1 P
        (GlobalTheory.DefLiftHecke.one_pow_notMem P 0) (fun PP hPP => hgood PP hPP)).2.1 _ d Rr).1 hR).2
    have hlab : GlobalTheory.Hk3.IsLab (Vc D i) P d := ⟨Rr, hsp⟩
    have hK0 := GlobalTheory.SphLabelOps.exists_hyp (Vc D i) P
    obtain ⟨K, hK⟩ := hK0
    have hsp' := hsp
    unfold GlobalTheory.Hk3.SphOp Hecke₂ at hsp'
    obtain ⟨e, f, ϖ, α, _, hpi, hϖ, hϖ2, _, _, _, hα, hdα, _, _⟩ := hsp'
    have r1 := GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi hϖ hϖ2 hα hdα hsp
    have r2 := GlobalTheory.SphLabelOps.reps_of_sphOp hK hpi hϖ hϖ2 hα hdα (GlobalTheory.Hk3.LabDet.sphOp_rep hlab)
    funext g
    have hsum : ∑ γ ∈ Rr, l ((R.extV i t) y (g * γ)) =
        ∑ γ ∈ GlobalTheory.Hk3.rep (Vc D i) P d, l ((R.extV i t) y (g * γ)) := by
      have h0 := r1.sum_eq r2 K.one_mem (fun γ => l ((R.extV i t) y (g * γ)))
        (fun x k hk => by
          simpa only [mul_assoc] using hfix P hgood k (by rw [hK]; exact hk) (g * x))
      simpa only [one_mul] using h0
    have hop : GlobalTheory.Hk3.hkF (Vc D i) P (fun₀ | d => 1) ((R.HV i t).e y) = s P d • (R.HV i t).e y :=
      Eq.trans (Eq.symm (hh P hgood (fun₀ | d => 1) y))
        (Eq.trans (congrArg (⇑(R.HV i t).e) (hy P d hgood hlab)) (map_smul (R.HV i t).e (s P d) y))
    have hext := GlobalTheory.DefLiftHecke.ext_hkF (R.cV i) hc P (fun₀ | d => 1) ((R.HV i t).e y) g
    have hext2 : s P d • (R.cV i).ext ((R.HV i t).e y) g =
        ∑ a ∈ GlobalTheory.Hk3.rep (Vc D i) P d, (R.cV i).ext ((R.HV i t).e y) (g * a) := by
      have h0 := (congrArg (fun z => (R.cV i).ext z g) hop).symm.trans hext
      simpa only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
        one_smul, map_smul, Pi.smul_apply, LinearMap.smul_apply] using h0
    show ∑ γ ∈ Rr, l ((R.extV i t) y (g * γ)) = s P d • l ((R.extV i t) y g)
    refine hsum.trans ?_
    show ∑ γ ∈ GlobalTheory.Hk3.rep (Vc D i) P d, l ((R.cV i).ext ((R.HV i t).e y) (g * γ)) =
      s P d • l ((R.cV i).ext ((R.HV i t).e y) g)
    exact (map_sum l (fun γ => (R.cV i).ext ((R.HV i t).e y) (g * γ)) (GlobalTheory.Hk3.rep (Vc D i) P d)).symm.trans
      ((congrArg l hext2.symm).trans (map_smul l (s P d) _))

end GlobalTheory.LiftParams
