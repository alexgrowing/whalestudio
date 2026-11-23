import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RetieVolTieGAndCdScaleTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasures
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import CompanionTheory.AutomorphicTheory.SiegelUnitTheory.VolumeSignatureIndependent

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.V

theorem pi_cd_eq_map (D : D7) (V : HSp D) (hV : V.SigOK) (μ1 : Measure (GA D V))
    (hμ1 : IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ1)
    (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hc : Continuous rp) (hrp : IsRealPart V θ A rp) :
    Measure.pi (fun ρ : D.what₂.Tau => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) =
      Measure.map rp (μ1.restrict (Stab V)) := by
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hsc
  haveI := hbo
  haveI : ∀ ρ : D.what₂.Tau, SigmaFinite (D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := fun ρ => by
    haveI := D.cd.haar (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    infer_instance
  have hφm : Measurable rp := hc.measurable
  obtain ⟨-, -, H⟩ := hμ1
  obtain ⟨-, H1⟩ := H θ hθ
  have H2 := H1 A hA
  refine Measure.pi_eq fun B hB => ?_
  have hm : MeasurableSet (rp ⁻¹' Set.univ.pi B) := hφm (MeasurableSet.univ_pi hB)
  rw [Measure.map_apply hφm (MeasurableSet.univ_pi hB), Measure.restrict_apply hm]
  refine Eq.trans ?_ (H2 B hB)
  congr 1
  ext h
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
  rw [and_comm]
  refine and_congr Iff.rfl (forall_congr' fun ρ => ⟨fun hb => ⟨rp h ρ, hb, hrp h ρ⟩, ?_⟩)
  rintro ⟨b, hb, hbe⟩
  rwa [GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ (hbe.trans (hrp h ρ).symm)] at hb

end MainStatements.Tam.V

namespace MainStatements.Tam

theorem vol : VolSt := by
  intro D V P Q hV hs μ _ 𝓕 h𝓕 θ A m rp hθ hA hm hc hrp B hB
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨hlc, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hlc
  haveI := hsc
  haveI := hbo
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _

  have hTG : VolTieG (GlobalTheory.Mem.retie D) := (GlobalTheory.Mem.retie_volTieG_and_cdScaleTie D).1
  have hT : VolTie (GlobalTheory.Mem.retie D) := VolTieG.volTie hTG
  have h2 : Conclusion2 (GlobalTheory.Mem.retie D) := volumeMass_of_unfolding _ (CompanionTheory.HU.mass_ratio_under_volume _ hT)
  have hrk : V.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum V hV D.host.φ₀
    rw [hs D.host.φ₀] at this
    exact this.symm
  have hvol : (GlobalTheory.Mem.retie D).vol V = massI D V.rank := by
    rw [hrk]
    exact GlobalTheory.Glob.vol_eq_massI_all_sig (GlobalTheory.Mem.retie D) hT h2 V P Q hV hs

  have hTG' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome
      (IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2)) fun μ1 : Measure (GA D V) =>
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (fun 𝓕 : Set (GA D V) => IsFundamentalDomain (GQ V) 𝓕 μ1) fun 𝓕 =>
        μ1 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol V) := hTG V hV
  obtain ⟨⟨μ1, hμ1'⟩, Hvol⟩ := hTG'
  haveI := hμ1'.1

  have hscale : μ = Measure.haarScalarFactor μ μ1 • μ1 := Measure.isMulLeftInvariant_eq_smul μ μ1
  have hc0 : ((Measure.haarScalarFactor μ μ1 : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ1).ne'
  have hμX : ∀ X, μ X = (Measure.haarScalarFactor μ μ1 : ℝ≥0∞) * μ1 X := fun X => by
    conv_lhs => rw [hscale]
    first
      | rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      | simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
      | simp [Measure.smul_apply]
  have hac : μ1 ≪ μ := fun X hX => by
    rw [hμX] at hX
    exact (mul_eq_zero.1 hX).resolve_left hc0
  have h𝓕1 : IsFundamentalDomain (GQ V) 𝓕 μ1 := h𝓕.mono hac
  have hF1 : μ1 𝓕 = ENNReal.ofReal ((GlobalTheory.Mem.retie D).vol V) := (Hvol μ1 hμ1').2 𝓕 h𝓕1

  have hpi := MainStatements.Tam.V.pi_cd_eq_map D V hV μ1 hμ1' θ A rp hθ hA hc hrp
  have hSet : μ {h | h ∈ Stab V ∧ rp h ∈ B} = (Measure.haarScalarFactor μ μ1 : ℝ≥0∞) *
      Measure.pi (fun ρ : D.what₂.Tau => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) B := by
    rw [hμX, hpi, Measure.map_apply hc.measurable hB, Measure.restrict_apply (hc.measurable hB)]
    congr 2
    ext h
    exact and_comm

  have hVpos : 0 < ReciprocityTheory.ChartRestriction.DS.volU V.rank := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.volU_pos V.rank
  have hmeq : ∀ ρ, m ρ = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank) •
      D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 := fun ρ => by
    have e := GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd D.cd _ _ (m ρ) (hm ρ)
    rw [Formalism.BasicNotions.sig_sum V hV (tauE D ρ)] at e
    exact e
  haveI : ∀ ρ : D.what₂.Tau, SigmaFinite (D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := fun ρ => by
    haveI := D.cd.haar (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    infer_instance
  haveI : ∀ ρ, SigmaFinite (m ρ) := fun ρ => by
    haveI := (hm ρ).1
    infer_instance
  have hpim : Measure.pi m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank) ^ D.R.f •
      Measure.pi (fun ρ : D.what₂.Tau => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) := by
    refine Measure.pi_eq fun C hC => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
    simp_rw [hmeq, Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
  rw [hpim, hSet, hμX 𝓕, hF1, hvol, Measure.smul_apply, smul_eq_mul,
    ENNReal.ofReal_mul (pow_nonneg hVpos.le _), ENNReal.ofReal_pow hVpos.le]
  ring

end MainStatements.Tam

end
